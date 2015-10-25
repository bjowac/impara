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
   *             -----------------------
   *                    root
   *  =>
   * byte_update(e, i, v', t)
   */
  if(dest.id()==ID_byte_update_little_endian
  || dest.id()==ID_byte_update_big_endian)
  {

    exprt &root=dest.op0();
    exprt &offset=dest.op1();
    const typet &type=root.type();

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

  }
  
  if(!step.is_hidden())
  {
    // wp(assume c, x) = c=>x
    if(step.guard.is_not_nil())
    {
      exprt negated_guard=not_exprt(step.guard);

      impara_disjoin(negated_guard, wp, ns);
    }
  }
  
  return wp;
}
