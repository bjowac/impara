
/*******************************************************************\

Module: Simple rules for wordlevel interpolation

Author: Georg Weissenbacher, georg@weissenbacher.name
        Mark Kattenbelt, mark.kattenbelt@comlab.ox.ac.uk

\*******************************************************************/

#include <util/simplify_expr.h>
#include <util/simplify_expr_class.h>
#include <util/mp_arith.h>
#include <util/arith_tools.h>
#include <util/bitvector.h>
#include <util/std_expr.h>
#include <util/std_types.h>

#include "wordlevel_interpolator.h"

//#define DEBUG

/*******************************************************************\

Function: added_constant_rulet::rewrite_term

  Inputs: 

 Outputs: 

 Purpose: Tries to match a term t+c, where c is a constant != 0.
          If it succeeds, it adds t!=t+c as an axiom and returns 
          false.

\*******************************************************************/
bool added_constant_rulet::rewrite_term
  (unsigned index, wordlevel_factt::partitiont partition,
   graph_axiomst& axioms)
{
  const exprt term=expression_pool[index];

  if (term.id()==ID_plus|| term.id()==ID_minus)
  {
    // sum up the 
    exprt sum=exprt(term.id(), term.type());
      
    exprt constant;
    bool has_constants=false;

    for (exprt::operandst::const_iterator it=term.operands().begin();
         it!=term.operands().end(); it++)
    {
      if (it->is_constant())
      {
        if (!has_constants)
        {
          constant=*it;
          has_constants=true;
        }
        else
          constant.sum(*it);
      }
      else
        sum.copy_to_operands(*it);
    }

    if (!has_constants || sum.operands().size()==0)
      return true;

    if (sum.operands().size()==1)
    {
      exprt tmp=sum.op0();
      sum.swap(tmp);
    }

    graph_factt fact;

    fact.n=index;
    fact.m=expression_pool.number(sum, partition);
    fact.partition=partition;
    fact.derivation=wordlevel_factt::THEORY_FACT;

    // check the sum
    fact.rel=constant.is_zero()?
      (graph_factt::EQUAL):(graph_factt::NOT_EQUAL);

#ifdef DEBUG    
    std::cout << " Adding axiom " << fact.n 
              << " " << fact.relation_to_string(fact.rel) << " "
              << fact.m << std::endl;
#endif

    axioms.add_axiom(fact, fact.m);

    return false;
  }

  return true;
}

/*******************************************************************\

Function: bitseq_extract_rulet::rewrite_term

  Inputs: 

 Outputs: 

 Purpose: Tries to find expressions where all bits are extracted
          from a variable (e.g., a[3:0] for a 4-bit variable).

\*******************************************************************/
bool bitseq_extract_rulet::rewrite_term
  (unsigned index, wordlevel_factt::partitiont partition,
   graph_axiomst& axioms)
{
  const exprt term=expression_pool[index];
  
  if (term.id()=="extractbits")
  {
    assert (term.operands().size()==3);

    mp_integer upper, lower;
    if(!simplify_exprt::is_bitvector_type(term.type()) ||
       to_integer(term.op1(), upper) || to_integer(term.op2(), lower))
      return true;

    const exprt &operand=term.op0();
    const typet &type=operand.type();

    if(!simplify_exprt::is_bitvector_type(type))
      return true;

    // redundant bit-extract?
    if((upper-lower+1)==to_bitvector_type(type).get_width())
    {
      graph_factt fact;

      fact.n=index;
      fact.m=expression_pool.number(operand, partition);
      fact.rel=graph_factt::EQUAL;
      fact.partition=partition;
      fact.derivation=wordlevel_factt::THEORY_FACT;
      
      axioms.add_axiom(fact, fact.m);

      return false;
    }
  }
  
  return true;
}


/*******************************************************************\

Function: bit_replication_rulet::term_rewrite

  Inputs: 

 Outputs: 

 Purpose: Tries to convert a replicated constant bit to a constant
          (Verilog only)

\*******************************************************************/
bool bit_replication_rulet::rewrite_term
  (unsigned index, wordlevel_factt::partitiont partition,
   graph_axiomst& axioms)
{
  const exprt term=expression_pool[index];
  
  if (term.id()=="replication" || term.id()=="concatenation")
  {
    exprt replication=term;
    if (!simplify_replication(replication))
    {
      graph_factt fact;

      fact.n=index;
      fact.m=expression_pool.number(replication, partition);
      fact.rel=graph_factt::EQUAL;
      fact.partition=partition;
      fact.derivation=wordlevel_factt::THEORY_FACT;
      
      axioms.add_axiom(fact, fact.m);
      return false;
    }
  }
  
  return true;
}

/*******************************************************************\

Function: bit_replication_rulet::simplify_concatenation

  Inputs: 

 Outputs: 

 Purpose: Tries to eliminate a concatenation and returns 
          false if it succeeds

\*******************************************************************/

bool bit_replication_rulet::simplify_concatenation
(exprt &concatenation) const
{
  if(concatenation.type().id()!=ID_unsignedbv)
    return true;

  if(concatenation.is_constant())
    return false;

  unsigned width=0;
  std::string value_string;
  
  forall_operands(o_it, concatenation)
  {
    exprt operand=*o_it;
    if(simplify_replication(operand))
      return true;

    width+=bv_width(operand.type());
    value_string+=operand.get(ID_value).c_str();
  }

  assert(width==to_bitvector_type(concatenation.type()).get_width());
  
  mp_integer value=string2integer(value_string, 2);
  exprt tmp=from_integer(value, concatenation.type());
  concatenation.swap(tmp);
  return false;
}

/*******************************************************************\

Function: bit_replication_rulet::simplify_replication

  Inputs: 

 Outputs: 

 Purpose: Tries to eliminate a replication and returns 
          false if it succeeds

\*******************************************************************/
bool bit_replication_rulet::simplify_replication
(exprt& replication) const
{
  if(replication.type().id()!="unsignedbv")
    return true;

  if(replication.is_constant())
    return false;

  if(replication.id()=="concatenation")
    return simplify_concatenation(replication);

  assert (replication.operands().size()==2);

  mp_integer counter;
  assert (!to_integer(replication.op0(), counter));

  exprt &replicand=replication.op1();

  if(simplify_replication(replicand))
    return true;

  exprt concatenation(ID_concatenation, replication.type());
  // reduce this to concatenation
  for (unsigned i=0; counter>i; i++)
    concatenation.copy_to_operands(replicand);
  
  if (!simplify_concatenation(concatenation))
  {
    replication.swap(concatenation);
    return false;
  }
  return true;
}

/*******************************************************************\

Function: null_pointer_cast_rulet::rewrite_term

  Inputs: 

 Outputs: 

 Purpose: Rewrites (int)NULL to 0 of type integer 

\*******************************************************************/
bool null_pointer_cast_rulet::rewrite_term
  (unsigned index, wordlevel_factt::partitiont partition,
   graph_axiomst& axioms)
{
  const exprt term=expression_pool[index];
  graph_factt fact;

  if(term.id()==ID_typecast && 
     simplify_exprt::is_bitvector_type(term.type()) &&
     term.op0().is_constant() &&
     term.op0().get(ID_value)==ID_NULL)
  {
    exprt constant=from_integer(0, term.type());

    fact.rel=graph_factt::EQUAL;
    fact.n=index;
    fact.m=expression_pool.number(constant, partition);
    fact.partition=partition;
    fact.derivation=wordlevel_factt::THEORY_FACT;

    axioms.add_axiom(fact, fact.m);
    return false;
  }
  
  return true;
}

/*******************************************************************\

Function: bitvec_upcast_rulet::rewrite_fact

  Inputs: 

 Outputs: 

 Purpose: Tries to find a relation where two parameters of
          equal type are cast up (promoted) to another equal
          type:
          (n-bit)(a: m-bit) R (n-bit)(b: m-bit)
          -------------------------------------
                 (a: m-bit) R (b: m-bit)
          This rule also tries to deal with constants that
          can be downcast.

\*******************************************************************/
bool bitvec_upcast_rulet::rewrite_fact
(const graph_factt& fact, graph_axiomst& axioms)
{
  const exprt left=expression_pool[fact.n];
  const exprt right=expression_pool[fact.m];

  if(!simplify_exprt::is_bitvector_type(left.type()) ||
     !simplify_exprt::is_bitvector_type(right.type()) ||
     (left.id()!=ID_typecast && right.id()!=ID_typecast))
    return true;

  // we only rewrite toplevel-facts
  if(fact.derivation!=wordlevel_factt::TOPLEVEL_FACT)
    return true;

  graph_factt new_fact;
  
  new_fact.rel=fact.rel;
  new_fact.partition=fact.partition;
  new_fact.derivation=wordlevel_factt::TOPLEVEL_FACT;
      
  if(left.id()==ID_typecast && right.id()==ID_typecast)
  {
    if(left.op0().type()==right.op0().type())
    {
      new_fact.n=expression_pool.number(left.op0(), fact.partition);
      new_fact.m=expression_pool.number(right.op0(), fact.partition);

      axioms.add_axiom(new_fact, new_fact.n);
                       
      return false;
    }
  }
  else if (left.id()==ID_typecast && right.is_constant())
  {
    exprt constant=right;
    const typet &type=left.op0().type();
    if (!cast_constant(constant, type))
    {
      new_fact.n=expression_pool.number(left.op0(), fact.partition);
      new_fact.m=expression_pool.number(constant, fact.partition);

      axioms.add_axiom(new_fact, new_fact.n);

      return false;
    }
  }
  else if (right.id()==ID_typecast && left.is_constant())
  {
    exprt constant=left;
    if (!cast_constant(constant, right.op0().type()))
    {
      new_fact.n=expression_pool.number(constant, fact.partition);
      new_fact.m=expression_pool.number(right.op0(), fact.partition);

      axioms.add_axiom(new_fact, new_fact.m);

      return false;
    }
  }
    
  return true;
}

/*******************************************************************\

Function: bitvec_upcast_rulet::cast_constant

  Inputs: 

 Outputs: 

 Purpose: Tries to cast a constant to certain type
          and eleminate the typecast.
          Returns false it succeeds. Modifies
          the first parameter in either case.

\*******************************************************************/
bool bitvec_upcast_rulet::cast_constant
(exprt& constant, const typet& type) const
{
  if(constant.type().id()==ID_unsignedbv &&
     type.id()==ID_unsignedbv)
  {
    mp_integer value=binary2integer(id2string(constant.get(ID_value)), false);
    
    if(value<power(2, to_unsignedbv_type(type).get_width()))
    {
      constant=from_integer(value, type);
      return false;
    }
  }
  else if(constant.type().id()==ID_unsignedbv && type.id()==ID_bool)
  {
    mp_integer value=binary2integer(id2string(constant.get(ID_value)), false);

    if(value!=0)
      constant.make_true();
    else
      constant.make_false();
  }
  else if(constant.type().id()==ID_signedbv && type.id()==ID_signedbv)
  {
    unsigned width=to_signedbv_type(type).get_width();
    mp_integer value=binary2integer(id2string(constant.get(ID_value)), true);
    
    if(value>=(-power(2, width-1)) && 
       value<=(power(2, width-1)-1))
    {
      constant=from_integer(value, type);
      return false;
    }
  }
  else if(constant.type().id()==ID_signedbv && type.id()==ID_unsignedbv)
  {
    unsigned width=to_signedbv_type(type).get_width();
    mp_integer value=binary2integer(id2string(constant.get(ID_value)), true);

    if(value>=0 && value<(power(2, width)))
    {
      constant=from_integer(value, type);
      return false;
    }
  }

  return true;
}

/*******************************************************************\

Function: cond_cast_rulet::rewrite_fact

  Inputs: 

 Outputs: 

 Purpose: Removes the typecast from (int)x >(=) constant if possible

\*******************************************************************/
bool conditional_cast_rulet::rewrite_fact
(const graph_factt& fact, graph_axiomst& axioms)
{
  const exprt left=expression_pool[fact.n];
  const exprt right=expression_pool[fact.m];
  
  if(!simplify_exprt::is_bitvector_type(left.type()) ||
     !simplify_exprt::is_bitvector_type(right.type()) ||
     (left.id()!=ID_typecast && right.id()!=ID_typecast))
    return true;
  
  // we only rewrite toplevel-facts
  if(fact.derivation!=wordlevel_factt::TOPLEVEL_FACT)
    return true;

  graph_factt new_fact;
  
  new_fact.rel=fact.rel;
  new_fact.partition=fact.partition;
  new_fact.derivation=wordlevel_factt::TOPLEVEL_FACT;  

  if(fact.rel==graph_factt::GREATER_THAN ||
     fact.rel==graph_factt::GREATER_EQUAL_THAN)
  {
    if (left.id()==ID_typecast && right.is_constant())
    {
      exprt constant=right;
      const typet &type=left.op0().type();
      if (type.id()==ID_unsignedbv && 
          left.type().id()==ID_signedbv &&
          !cast_constant(constant, type))
      {
        new_fact.n=expression_pool.number(left.op0(), fact.partition);
        new_fact.m=expression_pool.number(constant, fact.partition);

        axioms.add_axiom(new_fact, new_fact.n);
        
        return false;
      }
    }
  }
    
  return true;  
}

/*******************************************************************\

Function: conditional_cast_rulet::cast_constant

  Inputs: 

 Outputs: 

 Purpose: Tries to cast a constant to certain type
          and eleminate the typecast.
          Returns false it succeeds. Modifies
          the first parameter in either case.

\*******************************************************************/
bool conditional_cast_rulet::cast_constant
(exprt& constant, const typet& type) const
{
  if(constant.type().id()==ID_signedbv &&
     type.id()==ID_unsignedbv)
  {
    mp_integer value=binary2integer(id2string(constant.get(ID_value)), false);
   
    if(value>=0 &&
       to_unsignedbv_type(type).get_width()>=to_signedbv_type(constant.type()).get_width())
    {
      constant=from_integer(value, type);
      return false;
    }
  }

  return true;
}

/*******************************************************************\

Function: struct_with_rulet::rewrite_fact

  Inputs:

 Outputs:

 Purpose: Tries to deal with with_exprt over structs

\*******************************************************************/

bool struct_with_rulet::rewrite_fact
(const graph_factt& fact, graph_axiomst& axioms)
{
  // we only rewrite toplevel-facts
  if(fact.derivation!=wordlevel_factt::TOPLEVEL_FACT ||
     fact.rel!=graph_factt::EQUAL)
    return true;

  const exprt left=expression_pool[fact.n];
  const exprt right=expression_pool[fact.m];

  const typet left_type=expression_pool.ns.follow(left.type());
  const typet right_type=expression_pool.ns.follow(right.type());

  if(left_type.id()!=ID_struct || right_type.id()!=ID_struct)
    return true;

  // use a heuristic to find out which operand is the target
  if(left.id()==ID_symbol || left.id()==ID_member || left.id()==ID_index)
  {
    if(right.id()==ID_with && 
       right.has_operands() && right.operands().size()==3)
      return rewrite_with_fact(fact, left, right, axioms);
    else
      return rewrite_struct_fact(fact, left, right, axioms);
  }
  
  if(right.id()==ID_symbol || right.id()==ID_member || right.id()==ID_index)
  {
    if(left.id()==ID_with && 
       left.has_operands() && left.operands().size()==3)
      return rewrite_with_fact(fact, right, left, axioms);
    else
      return rewrite_struct_fact(fact, right, left, axioms);
  }

  return true;
}

/*******************************************************************\

Function: struct_with_rulet::rewrite_with_fact

  Inputs:

 Outputs:

 Purpose: Tries to deal with with_exprt over structs. 
          Returns false on success.

\*******************************************************************/

bool struct_with_rulet::rewrite_with_fact
(const graph_factt& fact, 
 const exprt& target, const exprt& source, 
 graph_axiomst& axioms)
{
  const with_exprt &with=to_with_expr(source);

  const exprt &where=with.where();
  const exprt &value=with.new_value();
  const irep_idt &component_name=where.get(ID_component_name);

  const typet &target_type=expression_pool.ns.follow(target.type());
  const struct_typet &type=to_struct_type(target_type);
  const struct_typet::componentst &components=type.components();
  
  for (struct_typet::componentst::const_iterator
         c_it=components.begin(); 
       c_it!=components.end(); 
       ++c_it)
  {
    const irep_idt &name=c_it->get_name();
    member_exprt lhs(target, name);
    lhs.type()=type.component_type(name);

    exprt rhs;
   
    if(c_it->get_name()==component_name)
      rhs=value;
    else
    {
      rhs=member_exprt(with.op0(), name);    
      rhs.type()=type.component_type(name);
    }

    graph_factt new_fact;

    new_fact.rel=graph_factt::EQUAL;
    new_fact.partition=fact.partition;
    new_fact.derivation=wordlevel_factt::TOPLEVEL_FACT;

    new_fact.n=expression_pool.number(lhs, fact.partition);
    new_fact.m=expression_pool.number(rhs, fact.partition);

#ifdef DEBUG
    std::cout << "Rewriter adds " 
              << from_expr(expression_pool.ns, "", lhs) 
              << "="
              << from_expr(expression_pool.ns, "", rhs) << std::endl;
#endif    

    axioms.add_axiom(new_fact, 0);
  }

  return (components.size()==0);  
}

/*******************************************************************\

Function: struct_with_rulet::rewrite_struct_fact

  Inputs:

 Outputs:

 Purpose: Tries to deal with assignments of structures

\*******************************************************************/

bool struct_with_rulet::rewrite_struct_fact
(const graph_factt& fact, 
 const exprt& target, const exprt& source, 
 graph_axiomst& axioms)
{
  const typet &target_type=expression_pool.ns.follow(target.type());
  const struct_typet &type=to_struct_type(target_type);
  const struct_typet::componentst &components=type.components();

  if(source.id()==ID_symbol || source.id()==ID_member)
  {
    for (struct_typet::componentst::const_iterator
           c_it=components.begin(); 
         c_it!=components.end(); 
         ++c_it)
    {
      const irep_idt &name=c_it->get_name();
      member_exprt lhs(target, name);
      lhs.type()=type.component_type(name);
      
      member_exprt rhs(source, name);
      rhs.type()=type.component_type(name);

#ifdef DEBUG
    std::cout << "Rewriter adds " 
              << from_expr(expression_pool.ns, "", lhs) 
              << "=" 
              << from_expr(expression_pool.ns, "", rhs) << std::endl;
#endif    
      
      graph_factt new_fact;
      
      new_fact.rel=graph_factt::EQUAL;
      new_fact.partition=fact.partition;
      new_fact.derivation=wordlevel_factt::TOPLEVEL_FACT;
      
      new_fact.n=expression_pool.number(lhs, fact.partition);
      new_fact.m=expression_pool.number(rhs, fact.partition);

      axioms.add_axiom(new_fact, 0);
    }

    return (components.size()==0);  
  }
  else if (source.has_operands() &&   
           source.operands().size() == components.size())
  {
    exprt::operandst::const_iterator o_it=source.operands().begin();
    
    for (struct_typet::componentst::const_iterator
           c_it=components.begin(); 
         c_it!=components.end(); 
         ++c_it, ++o_it)
    {
      const irep_idt &name=c_it->get_name();
      member_exprt lhs(target, name);
      lhs.type()=type.component_type(name);
      
      const exprt &rhs=*o_it;

#ifdef DEBUG
    std::cout << "Rewriter adds " 
              << from_expr(expression_pool.ns, "", lhs) 
              << "=" 
              << from_expr(expression_pool.ns, "", rhs) << std::endl;
#endif    
      
      graph_factt new_fact;
      
      new_fact.rel=graph_factt::EQUAL;
      new_fact.partition=fact.partition;
      new_fact.derivation=wordlevel_factt::TOPLEVEL_FACT;
      
      new_fact.n=expression_pool.number(lhs, fact.partition);
      new_fact.m=expression_pool.number(rhs, fact.partition);

      axioms.add_axiom(new_fact, 0);
    }

    return (components.size()==0);  
  }
  
  return true;
}

/*******************************************************************\

Function: bitwise_conjunction_rulet::rewrite_fact

  Inputs:

 Outputs:

 Purpose: i = x & y  --> i <= x && i <= y
          i = x | y  --> i >= x && i >= y

\*******************************************************************/

bool bitwise_conjunction_rulet::rewrite_fact
(const graph_factt& fact, graph_axiomst& axioms)
{
  bool unsuccessful=true;

  // we only rewrite toplevel-facts
  if(fact.derivation!=wordlevel_factt::TOPLEVEL_FACT ||
     fact.rel!=graph_factt::EQUAL)
    return true;

  const exprt left=expression_pool[fact.n];
  const exprt right=expression_pool[fact.m];

  if(left.type()!=right.type() ||
     left.type().id()!=ID_unsignedbv)
    return true;

  graph_factt new_fact;
  new_fact.rel=graph_factt::GREATER_EQUAL_THAN;    
  new_fact.partition=fact.partition;
  new_fact.derivation=wordlevel_factt::TOPLEVEL_FACT;

  if(left.id()==ID_bitand)
  {
    // left1 & left2 = right --> right <= leftx
    new_fact.m=expression_pool.number(right, fact.partition);

    forall_operands(it, left)
    {
      const exprt &operand=*it;
      assert(right.type()==operand.type());

      new_fact.n=expression_pool.number(operand, fact.partition);

      // operand >= right
      axioms.add_axiom(new_fact, new_fact.n);
      unsuccessful=false;
    }
  }
  else if(left.id()==ID_bitor)
  {
    // left1 | left2 = right --> right >= leftx
    new_fact.n=expression_pool.number(right, fact.partition);

    forall_operands(it, left)
    {
      const exprt &operand=*it;
      assert(right.type()==operand.type());

      new_fact.m=expression_pool.number(operand, fact.partition);

      // right >= operand
      axioms.add_axiom(new_fact, new_fact.m);
      unsuccessful=false;
    }
  }

  if(right.id()==ID_bitand)
  {
    // left = right1 & right2 --> left <= rightx
    new_fact.m=expression_pool.number(left, fact.partition);

    forall_operands(it, right)
    {
      const exprt &operand=*it;
      assert(left.type()==operand.type());

      new_fact.n=expression_pool.number(operand, fact.partition);

      // operand >= left
      axioms.add_axiom(new_fact, new_fact.n);
      unsuccessful=false;
    }
  }
  else if(right.id()==ID_bitor)
  {
    // left = right1 | right2 --> left >= rightx
    new_fact.n=expression_pool.number(left, fact.partition);

    forall_operands(it, right)
    {
      const exprt &operand=*it;
      assert(left.type()==operand.type());

      new_fact.m=expression_pool.number(operand, fact.partition);

      // left >= operand
      axioms.add_axiom(new_fact, new_fact.m);
      unsuccessful=false;
    }
  }
  
  return unsuccessful; 
}

/*******************************************************************\

Function: shift_rulet::rewrite_fact

  Inputs:

 Outputs:

 Purpose: y = (x >> constant) --> x >= y

\*******************************************************************/

bool shift_rulet::rewrite_fact
(const graph_factt& fact, graph_axiomst& axioms)
{
  // we only rewrite toplevel-facts
  if(fact.derivation!=wordlevel_factt::TOPLEVEL_FACT ||
     fact.rel!=graph_factt::EQUAL)
    return true;

  const exprt left=expression_pool[fact.n];
  const exprt right=expression_pool[fact.m];

  if(left.type().id()!=ID_unsignedbv || right.type().id()!=ID_unsignedbv)
    return true;

  graph_factt new_fact;
  new_fact.rel=graph_factt::GREATER_EQUAL_THAN;
  new_fact.partition=fact.partition;
  new_fact.derivation=wordlevel_factt::TOPLEVEL_FACT;

  bool status=true;

  if(left.id()==ID_shr || left.id()==ID_lshr || left.id()==ID_ashr)
  {
    new_fact.n=expression_pool.number(left.op0(), fact.partition);
    new_fact.m=fact.m;
    axioms.add_axiom(new_fact, new_fact.n);
    status=false;
  }
  
  if(right.id()==ID_shr || right.id()==ID_lshr || right.id()==ID_ashr)
  {
    new_fact.n=expression_pool.number(right.op0(), fact.partition);
    new_fact.m=fact.n;
    axioms.add_axiom(new_fact, new_fact.n);
    status=false;
  }

  return status;
}

/*******************************************************************\

Function: shift_rulet::rewrite_term

  Inputs: 

 Outputs: 

 Purpose: a >> 1 -->  a + a 

\*******************************************************************/
bool shift_rulet::rewrite_term
  (unsigned index, wordlevel_factt::partitiont partition,
   graph_axiomst& axioms)
{
  const exprt term=expression_pool[index];

  if(term.type().id()!=ID_unsignedbv)
    return true;

  if(term.id()==ID_shl && term.op1().is_constant())
  {
    mp_integer value=
      binary2integer(id2string(term.op1().get(ID_value)), false);
    if(value<bv_width(term.type()) && value>0)
    {
      exprt sum=exprt(ID_plus, term.type());
      sum.copy_to_operands(term.op0(), term.op0());

      for(--value; value>0; --value)
      {
        exprt tmp=sum;
        sum.op0()=tmp;
        sum.op1()=tmp;
      }

      simplify(sum, expression_pool.ns);
      
      graph_factt fact;
      
      fact.n=index;
      fact.m=expression_pool.number(sum, partition);
      fact.rel=graph_factt::EQUAL;
      fact.partition=partition;
      fact.derivation=wordlevel_factt::THEORY_FACT;
      
#ifdef DEBUG    
      std::cout << " Adding axiom " << fact.n 
                << " " << fact.relation_to_string(fact.rel) << " "
                << fact.m << std::endl;
#endif
      
      axioms.add_axiom(fact, fact.m);
      
      return false;
    }
  }

  return true;
}
