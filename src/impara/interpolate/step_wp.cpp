/*******************************************************************\

Module: Computing a WP of a step

Author: Daniel Kroening, kroening@kroening.com
        Bjorn Wachter, bjoern.wachter@gmail.com

\*******************************************************************/

#include <langapi/language_util.h>

#include <util/expr_util.h>
#include <util/simplify_expr.h>
#include <util/replace_expr.h>
#include <util/std_expr.h>
#include <util/prefix.h>
#include <util/find_symbols.h>

#include <solvers/flattening/bv_pointers.h>
#include <solvers/sat/satcheck.h>
#include <solvers/smt2/smt2_dec.h>
#include <solvers/smt2/smt2_conv.h>

#include "quantifier_elimination.h"

#include "impara_join.h"

#include "step_wp.h"

//#define DEBUG

#ifdef DEBUG
#include <iostream>
#endif



bool contains_if(exprt &dest,
		 const namespacet &ns)
{
  if(dest.id()==ID_if)
    return true;

  if(dest.has_operands())
    Forall_operands(it, dest)
      if (contains_if(*it, ns))
	return true;

  return false;
}


/*******************************************************************\

Function: rewrite_byte_expr

  Inputs: 

 Outputs: 

 Purpose:

\*******************************************************************/

void simplify_byte_expr(exprt &dest,
                        const namespacet &ns)
{

  /*
   * byte_update(byte_update(e, i, v, t), i, v', t) 
   *  =>
   * byte_update(e, i, v', t)
   */
  if(dest.id()==ID_byte_update_little_endian 
  || dest.id()==ID_byte_update_big_endian)
  {
  
    exprt &root=dest.op0();
    exprt &offset=dest.op1();
    const typet &type=dest.type();
  
    if(root.id()==ID_byte_update_little_endian 
    || root.id()==ID_byte_update_big_endian)
    {
      exprt &nested_root=root.op0();
      exprt &nested_offset=root.op1();
      const typet &nested_type=root.type();
      
      
      if(offset == nested_offset
      && type == nested_type)
      {
      
        #ifdef DEBUG
        std::cout << "simplify_byte_expr " << from_expr(dest) << std::endl;
        #endif
      
        root.swap(nested_root);
        
        #ifdef DEBUG
        std::cout << "  ==> " << from_expr(dest) << std::endl;
        #endif       
      }          
    }
  }
  
  /*
   * byte_extract(byte_update(e, i, v, t), i, t) 
   *  =>
   * v
   */
  else 
  if(dest.id()==ID_byte_extract_little_endian 
  || dest.id()==ID_byte_extract_big_endian)
  {
    exprt &root=dest.op0();
    exprt &offset=dest.op1();
    const typet &type=dest.type();
  
    if(root.id()==ID_byte_update_little_endian 
    || root.id()==ID_byte_update_big_endian)
    {
      exprt &nested_offset=root.op1();
      exprt &nested_with=root.op2();
      const typet &nested_type=root.type();
      
      
      if(offset == nested_offset
      && type == nested_type)
      {
        #ifdef DEBUG
        std::cout << "simplify_byte_expr " << from_expr(dest) << std::endl;
        #endif

        dest.swap(nested_with);
        
        //#ifdef DEBUG
        std::cout << "  ==> " << from_expr(dest) << std::endl;
        //#endif
      }          
    }
  }    

  if(dest.has_operands())
    Forall_operands(it, dest)
      simplify_byte_expr(*it, ns);
}
                       


/*******************************************************************\

Function: expand_if

  Inputs: 

 Outputs: 

 Purpose:
    Expand tri-state if-expressions using the rule:

    (c ? a : b) == f
    --------------
    (c ? a == f : b == f)

\*******************************************************************/


exprt simplified_if(
  const exprt &cond,
  const exprt &a,
  const exprt &b,
  const namespacet &ns)
{
  exprt lhs=cond;
  impara_conjoin(a, lhs, ns);
  exprt rhs=not_exprt(cond);
  impara_conjoin(b, rhs, ns);
  impara_disjoin(lhs, rhs, ns);
  
  return rhs;
}

void rewrite_if(exprt &dest,
              const namespacet &ns)
{


  if(dest.id()==ID_not)
  {
    rewrite_if(dest.op0(), ns);

    if(dest.op0().id() == ID_if)
    {
      const if_exprt &if_expr=to_if_expr(dest.op0());

      dest=if_exprt(if_expr.cond(), not_exprt(if_expr.true_case()), not_exprt(if_expr.false_case()));
    } 
  }
  else
  if(dest.id()==ID_equal || dest.id()==ID_notequal ||
     dest.id()==ID_gt || dest.id()==ID_lt ||
     dest.id()==ID_ge || dest.id()==ID_le)
  {
    assert(dest.operands().size()==2);

    if(dest.op0().id()==ID_typecast)
    {
      const typecast_exprt& tc=to_typecast_expr(dest.op0());

      if(dest.op1().type()!=tc.op0().type())
      {
        dest.op1()=typecast_exprt(dest.op1(), tc.op0().type());
      }
      
      dest.op0()=tc.op0();
      
      rewrite_if(dest, ns);
      
      return;

      if(tc.op0().id()==ID_if)
      {
	      const if_exprt &if_expr=to_if_expr(tc.op0());

        exprt a=binary_relation_exprt( typecast_exprt(if_expr.true_case(),tc.type()), dest.id(), dest.op1());
			  exprt b=binary_relation_exprt( typecast_exprt(if_expr.false_case(),tc.type()), dest.id(), dest.op1());
			  
			  rewrite_if(a, ns);
			  rewrite_if(b, ns);

	      dest=if_exprt(if_expr.cond(), a, b);
	      return;
      }
    }


    if(dest.op0().id()==ID_if) 
    {
      const if_exprt &if_expr=to_if_expr(dest.op0());

      exprt a=binary_relation_exprt( if_expr.true_case(), dest.id(), dest.op1());
      exprt b=binary_relation_exprt( if_expr.false_case(), dest.id(), dest.op1());

      rewrite_if(a, ns);
      rewrite_if(b, ns);
      
      dest=if_exprt(if_expr.cond(), a, b);
      return;
    } else if(dest.op1().id()==ID_if) 
    {
      const if_exprt &if_expr=to_if_expr(dest.op1());

      dest=if_exprt(if_expr.cond(), 
                    binary_relation_exprt( if_expr.true_case(), dest.id(), dest.op0()),
		                binary_relation_exprt( if_expr.false_case(), dest.id(), dest.op0()));
      return;
    } 
  }
    
  if(dest.has_operands())
    Forall_operands(it, dest)
      rewrite_if(*it, ns);
}


/*******************************************************************\

Function: strip_nested_casts

  Inputs: 

 Outputs: 

 Purpose:

\*******************************************************************/

const exprt& strip_nested_casts(const exprt& expr)
{
  if(expr.id()==ID_typecast)
  {
    strip_nested_casts(expr.op0());
  }

  return expr;
}



exprt original(const exprt &src)
{
  if(src.id()==ID_symbol)
  {
    const std::string &identifier=id2string(to_symbol_expr(src).get_identifier());
    std::size_t pos=identifier.rfind('#');
    if(pos==std::string::npos) return src;    
    return symbol_exprt(identifier.substr(0,pos), src.type());
  }
  
  if(src.has_operands())
  {
    exprt tmp=src;
  
    Forall_operands(it, tmp)
    {
      exprt tmp2=original(*it);
      *it=tmp2;
    }
    
    return tmp;
  }
  
  return src;
}

/*******************************************************************\

Function: step_wp

  Inputs: 

 Outputs: 

 Purpose:

\*******************************************************************/

exprt step_wp(
  const impara_stept &step,
  const exprt &cond,
  const namespacet &ns)
{
  exprt wp=cond;
  
  const symbol_exprt &ssa_lhs_symbol(to_symbol_expr(step.ssa_lhs));

  bool change=false;

  // wp(a:=b, x) = x[a<-b]
  if(step.full_lhs.is_not_nil() && has_symbol(ssa_lhs_symbol, wp))
  {

    // do we do a nondet-assignment?
    if (step.ssa_rhs.is_nil() || 
         (  
           step.ssa_rhs.id()==ID_symbol &&
           has_prefix(id2string(to_symbol_expr(step.ssa_rhs).get_identifier()), "symex::nondet")
         )
       ) 
    {
      wp=eliminate_forall(step.ssa_lhs, wp, ns);
    }
    else
    {
      replace_expr(step.ssa_lhs, step.ssa_rhs, wp);
      simplify(wp, ns);     
    }

    simplify_byte_expr(wp, ns);

    change=true;
  }
  
  if(!step.is_hidden())
  {
    // wp(assume c, x) = c=>x
    if(step.guard.is_not_nil())
    {
      exprt negated_guard=not_exprt(step.guard);

      impara_disjoin(negated_guard, wp, ns);

      change=true;
    }
  }
  
  if(change)
  { 
    rewrite_if(wp, ns);
  }
  
  return wp;
}
