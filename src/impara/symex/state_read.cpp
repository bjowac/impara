/*******************************************************************\

Module: State of path-based symbolic simulator

Author: Daniel Kroening, kroening@kroening.com
        Bjoern Wachter, bjoern.wachter@gmail.com

\*******************************************************************/

#include <util/string2int.h>
#include <util/simplify_expr.h>
#include <util/arith_tools.h>
#include <util/byte_operators.h>
#include <util/pointer_offset_size.h>
#include <util/mp_arith.h>
#include <util/expr_util.h>
#include <util/decision_procedure.h>
#include <util/i2string.h>
#include <util/find_symbols.h>
#include <util/replace_expr.h>
#include <util/base_type.h>
#include <util/prefix.h>

#include <goto-symex/rewrite_union.h>
#include <goto-symex/adjust_float_expressions.h>

#include <ansi-c/c_types.h>

#include <pointer-analysis/dereference.h>
#include "state.h"

#include "symex_data_structures.h"

#include "../nodes.h" // TODO: remove, culprit ssa_name

//#define DEBUG

#ifdef DEBUG
#include <iostream>
#include <langapi/language_util.h>
#endif


/*******************************************************************\

Function: statet::read

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt statet::read(const exprt &src, bool propagate)
{
  #ifdef DEBUG
  std::cout << " ============= statet::read " << (propagate ? "prop" : "no prop") << " " << from_expr(var_map.ns, "", src) << std::endl;
  #endif
  
  // This has four phases!
  // 1. Floating-point expression adjustment (rounding mode)
  // 2. Rewrite unions into byte operators
  // 3. Dereferencing, including propagation of pointers.
  // 4. Rewriting to SSA symbols
  // 5. Simplifier
  
  exprt tmp1=src;
  adjust_float_expressions(tmp1, var_map.ns);

  exprt tmp2=tmp1;
  rewrite_union(tmp2, var_map.ns);

  // we force propagation for dereferencing
  exprt tmp3=dereference_rec(tmp2, true);

#ifdef DEBUG
  std::cout << "   == deref ==> " << from_expr(var_map.ns, "", tmp3) << std::endl;
#endif

  exprt tmp4=instantiate_rec(tmp3, propagate);

#ifdef DEBUG
  std::cout << "   == instantiate ==> " << from_expr(var_map.ns, "", tmp3) << std::endl;
#endif
  
  exprt tmp5=  simplify_pointer_checks(tmp4);
  
  simplify(tmp5, var_map.ns);

  return tmp5;
}


/*******************************************************************\

Function: statet::instantiate_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt statet::instantiate_rec_data(
  const exprt &src,
  bool propagate)
{
  const typet &src_type=var_map.ns.follow(src.type());
  
  if(src_type.id()==ID_struct) // src is a struct
  {
    const struct_typet &struct_type=to_struct_type(src_type);
    const struct_typet::componentst &components=struct_type.components();
    
    struct_exprt result(src.type());
    result.operands().resize(components.size());

    // split it up into components
    for(unsigned i=0; i<components.size(); i++)
    {
      const typet &subtype=components[i].type();
      const irep_idt &component_name=components[i].get_name();

      exprt new_src;
      if(src.id()==ID_struct) // struct constructor?
      {
        assert(src.operands().size()==components.size());
        new_src=src.operands()[i];
      }
      else
        new_src=member_exprt(src, component_name, subtype);
      
      // recursive call
      result.operands()[i]=instantiate_rec(new_src, propagate);
    }

    return result; // done
  } 
  else if(src_type.id()==ID_array) // src is an array
  {
    const array_typet &array_type=to_array_type(src_type);
    const typet &subtype=array_type.subtype();
    
    if(array_type.size().is_constant())
    {
      mp_integer size;
      if(to_integer(array_type.size(), size))
        throw "failed to convert array size";
        
      unsigned long long size_int=integer2unsigned(size);
        
      array_exprt result(array_type);
      result.operands().resize(size_int);
    
      // split it up into elements
      for(unsigned long long i=0; i<size_int; ++i)
      {
        exprt index=from_integer(i, array_type.size().type());
        exprt new_src=index_exprt(src, index, subtype);
        
        // array constructor?
        if(src.id()==ID_array)
          new_src=simplify_expr(new_src, var_map.ns);
        
        // recursive call
        result.operands()[i]=instantiate_rec(new_src, propagate);
      }
      
      return result; // done
    }
    else
    {
      // TODO
    }
  }
  else if(src_type.id()==ID_vector) // src is a vector
  {
    const vector_typet &vector_type=to_vector_type(src_type);
    const typet &subtype=vector_type.subtype();
    
    if(!vector_type.size().is_constant())
      throw "vector with non-constant size";

    mp_integer size;
    if(to_integer(vector_type.size(), size))
      throw "failed to convert vector size";
      
    unsigned long long int size_int=integer2unsigned(size);
    
    vector_exprt result(vector_type);
    exprt::operandst &operands=result.operands();
    operands.resize(size_int);
  
    // split it up into elements
    for(unsigned long long i=0; i<size_int; ++i)
    {
      exprt index=from_integer(i, vector_type.size().type());
      exprt new_src=index_exprt(src, index, subtype);
      
      // vector constructor?
      if(src.id()==ID_vector)
        new_src=simplify_expr(new_src, var_map.ns);
      
      // recursive call
      operands[i]=instantiate_rec(new_src, propagate);
    }

    return result; // done
  }
  
  return nil_exprt();
}


/*******************************************************************\

Function: statet::instantiate_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt statet::instantiate_symbol(
  const symbol_exprt &symbol_expr,
  const std::string &suffix,
  const typet &final_type,
  bool propagate)
{
  bool is_ssa_symbol=symbol_expr.get_bool(ID_C_SSA_symbol);

  irep_idt identifier = is_ssa_symbol ?  // SSA already
                        symbol_expr.get(ID_C_full_identifier)
                      : symbol_expr.get_identifier();

  if(is_ssa_symbol && !propagate)
    return symbol_expr;

  if(has_prefix(id2string(identifier), "symex::nondet"))
    return symbol_expr;

  impara_var_mapt::var_infot &var_info=
    var_map(identifier, suffix, final_type);

  // warning: reference is not stable      
  var_statet &var_state=get_var_state(var_info);
  
  const exprt &value=var_state.value;

  #ifdef DEBUG
  std::cout << "instantiate_rec_symbol " << identifier
            << " var_info " << var_info.full_identifier
            << " value " << from_expr(var_map.ns, "", value) 
            << " symbol " << from_expr(var_map.ns, "", var_state.ssa_symbol)
            << std::endl;
  #endif

  if(propagate && value.is_not_nil())
  {
    return value; // propagate a value
  }
  else
  {
    // we do some SSA symbol
    if(var_state.ssa_symbol.get_identifier()==irep_idt())
    {
      // produce one
      var_state.ssa_symbol=var_info.ssa_symbol(current_thread, depth);
    }
        
    return var_state.ssa_symbol;
  }
}  


struct address_dividert
{
  address_dividert(const constant_exprt &__d)
  : d(__d)
  {
  }

  const constant_exprt &d;

  exprt operator()(const exprt &expr)
  {
		if(d==gen_one(d.type()))
			return expr;
  
    if(d.id()==ID_constant)
    {
      return plus(expr);
    }

    return nil_exprt();
  }

  // constant_exprt * expr + constant_exprt * expr
  exprt plus(const exprt &expr)
  {
    if(expr.id()==ID_plus)
    {
      exprt op0=plus(expr.op0());
      exprt op1=plus(expr.op1());
            
      return plus_exprt(op0, op1, expr.type());
    }
    else if(expr.id()==ID_mult)
    {
      return mult(expr);
    }
    else if(expr.id()==ID_typecast)
    {
			exprt tmp=expr;
    	exprt op0=plus(expr.op0());
    	tmp.op0().swap(op0);
    	return tmp;
    }
    
    else
    {
      return nil_exprt();
    }   
  }

  // constant * expr => constant/d * expr
  exprt mult(const exprt &expr)
  {
    if(expr.id()==ID_mult)
    {
      exprt op0=expr.op0();
      exprt op1=expr.op1();
 
      if(op0.id()==ID_constant || op1.id()==ID_constant)
      {
        if(op0.id()!=ID_constant)
        {
          op0.swap(op1);
        }
      
        const constant_exprt &constant_op0=to_constant_expr(op0);
    
        mp_integer int_value0, int_value1;
        bool ok0, ok1;

        ok0=!to_integer(constant_op0, int_value0);
        ok1=!to_integer(d, int_value1);
        
        if(ok0 && ok1)
        {
          mp_integer result=int_value0/int_value1;
          exprt tmp=from_integer(result, expr.type());
   
          return mult_exprt(tmp, op1);
          
        }

	return nil_exprt();
      }
    }

    return nil_exprt();  
 
  }
};
 
exprt statet::simplify_byte_extract(
  const exprt &src)
{ 
 
  const byte_extract_exprt &byte_extract=to_byte_extract_expr(src);
  const exprt &object=byte_extract.op();

  const typet &object_type=var_map.ns.follow(object.type());

  if(object_type.id()==ID_array)
  {
    const typet base_object_type=var_map.ns.follow(object_type.subtype());
    const typet element_type=var_map.ns.follow(byte_extract.type());
     
    const exprt &offset=byte_extract.offset();


    mp_integer element_width=pointer_offset_size(element_type, var_map.ns);
    std::string index_width=id2string(offset.type().get(ID_width));
    std::string byte_width_value=integer2binary(element_width,unsafe_string2unsigned(index_width));        
    constant_exprt byte_width=constant_exprt(byte_width_value,byte_extract.offset().type());
    address_dividert divider(byte_width);

    exprt index=divider(byte_extract.offset());
    
    if(!index.is_nil())
    {
      simplify(index, var_map.ns);
      
      //if(base_object_type!=element_type)
      return index_exprt(object, index, src.type());
    }
    else
    {
    
    
      #ifdef DEBUG
      std::cout << "byte_extract :-( " << from_expr(byte_extract)
                                   << "\n   * element type:\n "
                                   << element_type.pretty()
                                   << "\n   * width:\n"
                                   << from_expr(byte_width)
                                   << "\n   * offset:\n"
                                   << from_expr(byte_extract.offset()) 
                                   << "\n   * index:\n"
                                   << from_expr(index)<< std::endl;
      #endif                 
    }
  }  
  else 
  {
  }
  
  return src;
}
 

/*******************************************************************\

Function: statet::instantiate_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt statet::instantiate_rec(
  const exprt &src,
  bool propagate)
{
  #ifdef DEBUG
  std::cout << "instantiate_rec: "
            << from_expr(var_map.ns, "", src) << std::endl;
  #endif

  #ifdef SPLIT_DATA

  exprt tmp=instantiate_rec_data(src, propagate);
  
  if(tmp.is_not_nil())
    return tmp;

  // check whether this is a symbol(.member|[index])*
  
  {
    exprt tmp_symbol_member_index=
      read_symbol_member_index(src, propagate);
  
    if(tmp_symbol_member_index.is_not_nil())
      return tmp_symbol_member_index; // yes!
  }
  
  if(src.id()==ID_address_of)
  {
    assert(src.operands().size()==1);
    exprt tmp=src;
    tmp.op0()=instantiate_rec_address(tmp.op0(), propagate);
    
    #ifdef DEBUG
    std::cout << "instantiate_rec: ID_address_of ==> " << from_expr(tmp) << std::endl;
    #endif
    
    
    return tmp;
  }
  else if(src.id()==ID_side_effect)
  {
    // could be done separately
    const irep_idt &statement=to_side_effect_expr(src).get_statement();
    
    if(statement==ID_nondet)
    {        
      irep_idt id="symex::nondet"+i2string(nondet_count);
      ++nondet_count;
      return symbol_exprt(id, src.type());
    }
    else
      throw "instantiate_rec: unexpected side effect "
        + from_expr(var_map.ns, "", src);
  }
  else if(src.id()==ID_dereference)
  {
    // dereferencet has run already, so we should only be left with
    // integer addresses. Will transform into __CPROVER_memory[]
    // eventually.
  }
  else if(src.id()==ID_index)
  {
    // avoids indefinite recursion above
    return src;
  }
  else if(src.id()==ID_member)
  {
    const typet &compound_type=
      var_map.ns.follow(to_member_expr(src).struct_op().type());
      
    if(compound_type.id()==ID_struct)
    {  
      // avoids indefinite recursion above
      return src;
    }
    else if(compound_type.id()==ID_union)
    {
      member_exprt tmp=to_member_expr(src);
      tmp.struct_op()=instantiate_rec(tmp.struct_op(), propagate);
      return tmp;
    }
    else
    {
      throw "member expects struct or union type"+src.pretty();
    }
  }
  #endif
  
  #ifdef WITH_DATA
  if(src.id()==ID_symbol)
  {
    const symbol_exprt &symbol_expr=to_symbol_expr(src);
    const std::string suffix="";
    const typet &final_type=src.type();
    
    // don't touch function symbols
    if(var_map.ns.follow(final_type).id()==ID_code)
      return src;
    else
      return instantiate_symbol(symbol_expr, suffix, final_type, propagate);
  }
  else if(src.id()==ID_address_of)
  {
    assert(src.operands().size()==1);
    exprt tmp=src;
    tmp.op0()=instantiate_rec_address(tmp.op0(), propagate);
    return tmp;
  }
  else if(src.id()==ID_side_effect)
  {
    // could be done separately
    const irep_idt &statement=to_side_effect_expr(src).get_statement();
    
    if(statement==ID_nondet)
    {        
      irep_idt id="symex::nondet"+i2string(nondet_count);
      ++nondet_count;
      return symbol_exprt(id, src.type());
    }
    else
      throw "instantiate_rec: unexpected side effect "
      + from_expr(var_map.ns, "", src);
  }
  else if(src.id()==ID_index)
  {
    assert(src.operands().size()==2);
    exprt tmp=src;
    tmp.op0()=instantiate_rec(tmp.op0(), propagate);
    tmp.op1()=instantiate_rec(tmp.op1(), propagate);
    return tmp;
  }
  else if(src.id()==ID_byte_extract_little_endian 
       || src.id()==ID_byte_extract_big_endian)
  {
    exprt tmp=src; 
    tmp.op0()=instantiate_rec(tmp.op0(), propagate);
    tmp.op1()=instantiate_rec(tmp.op1(), propagate);
  
    return simplify_byte_extract(tmp);
  }
  else if(src.id()==ID_dereference)
  {
    // dereferencet has run already, so we should only be left with
    // integer addresses. Will transform into __CPROVER_memory[]
    // eventually.
  }
  #endif


  if(!src.has_operands())
    return src;

  exprt src2=src;
  
  // recursive calls on structure of 'src'
  Forall_operands(it, src2)
  {
    exprt tmp_op=instantiate_rec(*it, propagate);
    *it=tmp_op;
  }
  
  return src2;
}

/*******************************************************************\

Function: statet::read_symbol_member_index

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt statet::read_symbol_member_index(
  const exprt &src,
  bool propagate)
{
  std::string suffix="";
  exprt current=src;
  const typet final_type=src.type();
  exprt::operandst indices;
  
  // don't touch function symbols
  if(var_map.ns.follow(final_type).id()==ID_code)
    return nil_exprt();

  // the loop avoids recursion
  while(true)
  {
    exprt next=nil_exprt();
  
    if(current.id()==ID_symbol)
    {
      const symbol_exprt &symbol_expr=to_symbol_expr(current);
    
      return instantiate_symbol(symbol_expr, suffix, final_type, propagate);
    }
    else if(current.id()==ID_member)
    {
      const member_exprt &member_expr=to_member_expr(current);
      
      const typet &compound_type=
        var_map.ns.follow(member_expr.struct_op().type());
      
      if(compound_type.id()==ID_struct)
      { 
        // go into next iteration
        next=member_expr.struct_op();
        suffix="."+id2string(member_expr.get_component_name())+suffix;
      }
      else
        return nil_exprt(); // includes unions, deliberatley
    }
    else if(current.id()==ID_index)
    {
    
      #ifdef DEBUG
      std::cout << "read_symbol_member_index " << from_expr(current) << std::endl;
      #endif
    
      const index_exprt &index_expr=to_index_expr(current);
      
      exprt index_tmp=read(index_expr.index(), propagate);
      indices.push_back(index_tmp);
      
      std::string index_string=array_index_as_string(index_tmp);
      
      // go into next iteration
      next=index_expr.array();
      suffix=index_string+suffix;
    }
    else
    {
      return nil_exprt();
    }

    // next round  
    assert(next.is_not_nil());
    current=next;
  }
}

/*******************************************************************\

Function: statet::array_index_as_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string statet::array_index_as_string(const exprt &src) const
{
  exprt tmp=simplify_expr(src, var_map.ns);
  mp_integer i;

  if(!to_integer(tmp, i))
    return "["+integer2string(i)+"]";
  else
    return "[*]";
}


/*******************************************************************\

Function: strip_typecasts

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt strip_typecasts(const exprt &src)
{
  if(src.id()==ID_typecast)
  {
    return strip_typecasts(src.op0());
  }

  exprt src2=src;
  
  {
    // recursive calls on structure of 'src'
    Forall_operands(it, src2)
    {
      exprt tmp_op=strip_typecasts(*it);
      *it=tmp_op;
    }
  }

  return src2;
}

/*******************************************************************\

Function: strip_pointer_typecasts

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt strip_pointer_typecasts(const exprt &src)
{
  if(src.id()==ID_typecast)
  {
    exprt tmp=strip_pointer_typecasts(src.op0());
    
    if(tmp.type().id()==ID_pointer && src.type().id()!=ID_pointer)
      return tmp;
    else
      return typecast_exprt(tmp, src.type());
  }
  else
  if(src.id()==ID_plus)
  {
    exprt pointer=src.op0(), offset=src.op1();
    
    if(pointer.type().id()!=ID_pointer && offset.type().id()!=ID_pointer)
      return src;
       
    if(offset.type().id()==ID_pointer)
    {
      offset.swap(pointer);
    }

    return plus_exprt(pointer, offset, pointer.type());    
  }

  

  exprt src2=src;
  
  {
    // recursive calls on structure of 'src'
    Forall_operands(it, src2)
    {
      exprt tmp_op=strip_pointer_typecasts(*it);
      *it=tmp_op;
    }
  }
  
  return src2;
  
}


/*******************************************************************\

Function: statet::dereference_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt statet::dereference_rec(
  const exprt &src,
  bool propagate)
{
  if(src.id()==ID_dereference)
  {  
    const dereference_exprt &dereference_expr=to_dereference_expr(src);

    exprt address=dereference_expr.pointer();

    exprt address_dereferenced;

    try {

      if(address.id()==ID_plus)
      {
        address.op0()=read(address.op0(), propagate);
        address.op0()=::dereference(address.op0(), var_map.ns);
        if(address.op0().id()==ID_index)
        {
	  const exprt &base=address.op0().op0();
	  const exprt &index=address.op0().op1();
	  address_dereferenced=index_exprt(base, plus_exprt(index, address.op1()));
        }
        else
        {
          address_dereferenced=::dereference(dereference_expr.pointer(), var_map.ns);
        }
      }
      else
      {
        address=read(dereference_expr.pointer(), propagate);
        address_dereferenced=::dereference(address, var_map.ns);
      }
  
      #ifdef DEBUG
      
      std::cout << "   ::dereference " << from_expr(var_map.ns, "", dereference_expr.pointer()) 
                                       << " ==> " << from_expr(var_map.ns, "", address) << std::endl
                                       << " ==> " << from_expr(var_map.ns, "", address_dereferenced) << std::endl;
      #endif
      

    } catch(std::string &what)
    {  
      exprt address_prop=read(dereference_expr.pointer(), true);

      #ifdef DEBUG
      std::cout << "   dereference_rec : " 
                << from_expr(var_map.ns, "", dereference_expr.pointer()) 
                << " ==> " << from_expr(var_map.ns, "", address_prop) << std::endl;
      #endif
      
      try {
        address_dereferenced=::dereference(address_prop, var_map.ns);
      } catch(std::string &what)
      {
        // giving up: create a deref object
        symbolt value_symbol;

        value_symbol.base_name="deref"+i2string(dynamic_count);
        value_symbol.name="symex_dynamic::"+id2string(value_symbol.base_name);
        value_symbol.is_lvalue=true;
        value_symbol.type=var_map.ns.follow(src.type());
        value_symbol.type.set("#dynamic", true);
        value_symbol.mode=ID_C;

        std::cout << "   dereference_rec giving up on: " 
                << get_instruction()->source_location.as_string() 
                << from_expr(var_map.ns, "", address_prop) 
                << " ??? " << from_expr(var_map.ns, "", dereference_expr.pointer()) << std::endl;

	      return value_symbol.symbol_expr();
      }
	      
    }
   
    #ifdef DEBUG
    std::cout << "   dereference_rec : " << from_expr(var_map.ns, "", src) << " ==> " << from_expr(var_map.ns, "", address_dereferenced) << std::endl;
    #endif

   
    
    // the dereferenced address is a mixture of non-SSA and SSA symbols
    // (e.g., if-guards and array indices)
    return address_dereferenced;
  } 
  
  if(!src.has_operands())
    return src;

  exprt src2=src;
  
  {
    // recursive calls on structure of 'src'
    Forall_operands(it, src2)
    {
      exprt tmp_op=dereference_rec(*it, propagate);
      *it=tmp_op;
    }
  }
  
  return src2;
}

/*******************************************************************\

Function: statet::instantiate_rec_address

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt statet::instantiate_rec_address(
  const exprt &src,
  bool propagate)
{
  #ifdef DEBUG
  std::cout << "instantiate_rec_address: " << src.id() << std::endl;
  #endif

  if(src.id()==ID_symbol)
  {
    return src;
  } 
  else if(src.id()==ID_index)
  {
    assert(src.operands().size()==2);
    exprt tmp=src;
    tmp.op0()=instantiate_rec_address(src.op0(), propagate);
    tmp.op1()=instantiate_rec(src.op1(), false /*propagate*/);
    return tmp;
  }
  else if(src.id()==ID_dereference)
  {
    // dereferenct ran before, and this can only be *(type *)integer-address,
    // which we simply instantiate as non-address
    dereference_exprt tmp=to_dereference_expr(src);
    tmp.pointer()=instantiate_rec(tmp.pointer(), propagate);
    return tmp;
  }
  else if(src.id()==ID_member)
  {
    member_exprt tmp=to_member_expr(src);
    tmp.struct_op()=instantiate_rec_address(tmp.struct_op(), propagate);
    return tmp;
  }
  else if(src.id()==ID_string_constant)
  {
    return src;
  }
  else if(src.id()==ID_label)
  {
    return src;
  }
  else if(src.id()==ID_byte_extract_big_endian ||
          src.id()==ID_byte_extract_little_endian)
  {
    assert(src.operands().size()==2);
    exprt tmp=src;
    tmp.op0()=instantiate_rec_address(src.op0(), propagate);
    tmp.op1()=instantiate_rec(src.op1(), propagate);
    
    return simplify_byte_extract(tmp);
  }
  else if(src.id()==ID_if)
  {
    if_exprt if_expr=to_if_expr(src);
    if_expr.true_case()=instantiate_rec_address(if_expr.true_case(), propagate);
    if_expr.false_case()=instantiate_rec_address(if_expr.false_case(), propagate);
    if_expr.cond()=instantiate_rec(if_expr.cond(), propagate);
    return if_expr;
  }
  else if(src.id()==ID_typecast)
  {
    return to_typecast_expr(src).op();
  } 
  else {
    return src;
  }
}

/*******************************************************************\

Function: statet::collect_objects

  Inputs:

 Outputs:

 Purpose: ID_if ? obj_1 : ID_if ? obj_2 : obj_3 gives obj_1, obj_2, obj_3
 

\*******************************************************************/

void statet::collect_objects(const exprt &src, std::set<exprt> &result)
{
  if(src.id()==ID_if)
  {
    collect_objects(src.op1(), result);
    collect_objects(src.op2(), result);
  }
  else
  {
    result.insert(src);
  }
}


/*******************************************************************\

Function: statet::is_null

  Inputs:

 Outputs:

 Purpose: checks if an expression is NULL

\*******************************************************************/

bool statet::is_null(const exprt &src) const
{
  if(src.type().id()!=ID_pointer)
    return false;

  const exprt &obj=strip_typecasts(src);

  if(obj.is_zero())
    return true;

  if(obj.id()==ID_constant && obj.get(ID_value)==ID_NULL)
    return true;
    
  return false;
}


/*******************************************************************\

Function: statet::simplify_pointer_checks

  Inputs:

 Outputs:

 Purpose: using points-to information from statet we rewrite:
          * POINTER_OBJECT(&object) == POINTER_OBJECT(NULL)
            => FALSE
          * INVALID_OBJECT(&...)
            => FALSE

\*******************************************************************/

exprt statet::simplify_pointer_checks(const exprt &src)
{
  if(src.id()==ID_invalid_pointer)
  {
    exprt obj=read(src.op0());
  
    if(obj.id()==ID_address_of)
    {
      return false_exprt();
    }
    else if(is_null(obj))
    {
      return true_exprt();
    }
    else
    {
      return src;
    }
  }
  
  if(src.id()==ID_equal)
  {
    const exprt &lhs=src.op0();
    const exprt &rhs=src.op1();
    
    if(lhs.id()==ID_pointer_object && rhs.id()==ID_pointer_object)
    {
      exprt lhs_obj=read(lhs.op0());
      exprt rhs_obj=read(rhs.op0());
      
      std::set<exprt> objects;
      
      collect_objects(rhs_obj, objects);
      
      for(std::set<exprt>::const_iterator 
          it=objects.begin();
          it!=objects.end();
          ++it)
      {
        const exprt &other_obj=strip_pointer_typecasts(*it);

        exprt result=src;
      
        if(lhs_obj.id()==ID_address_of || lhs_obj.id()==ID_plus)
        {        
          if(is_null(other_obj))
            result=false_exprt();
          else if(other_obj.id()==ID_address_of && lhs_obj.op0()!=other_obj.op0())
            result=false_exprt();
        }
        
        return result;
      }  
    }    
  }
  
  exprt src2=src;
  
  {
    // recursive calls on structure of 'src'
    Forall_operands(it, src2)
    {
      exprt tmp_op=simplify_pointer_checks(*it);
      *it=tmp_op;
    }
  }
  
  return src2;
}


exprt statet::simplify_with(const exprt &src)
{
  if(src.id()==ID_with)
  {
    if(src.op1().id()==ID_constant)
    {
      exprt base=src.op0();
  
      mp_integer index;
      
      if(base.id()==ID_array 
         && !to_integer(to_constant_expr(src.op1()), index))
      {
        exprt tmp=base;
        
        unsigned long where=index.to_long();
        
        if(where<tmp.operands().size())
        {
          tmp.operands()[where]=src.op2();
        }
        
        return tmp; 
      }
    }
  } 
  
  if(src.id()==ID_index)
  {
    mp_integer index;
  
    if(src.op0().id()==ID_array && src.op1().id()==ID_constant)
    {
      if(!to_integer(to_constant_expr(to_constant_expr(src.op1())), index))
      {
        unsigned long where=index.to_long();
        if(where >= src.op0().operands().size())
          return nil_exprt();
      }
    } 
  }
  
  exprt src2=src;
  
  bool unknown=false;
  
  {
    // recursive calls on structure of 'src'
    Forall_operands(it, src2)
    {
      exprt tmp_op=simplify_with(*it);
      
      if(tmp_op.is_nil())
        unknown=true;
      
      *it=tmp_op;
    }
  }

  if(unknown)
    if(src.id()!=ID_struct && src.id()!=ID_array)
      return nil_exprt();
  
  return src2;
}



