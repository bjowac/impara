/*******************************************************************\

Module: Impara abstract domain

Author: Daniel Kroening, kroening@kroening.com
        Bjoern Wachter, bjoern.wachter@gmail.com

\*******************************************************************/

#include <langapi/language_util.h>


#include <util/simplify_expr.h>
#include <util/replace_expr.h>
#include <util/std_expr.h>
#include <util/prefix.h>
#include <util/expr_util.h>

#include "impara_join.h"

//#define DEBUG

#ifdef DEBUG
#include <iostream>
#endif


bool is_bv_op(const exprt &expr)
{

  bool result=true;
	
  forall_operands(it, expr)
  {
    const exprt &tmp=*it;
    const typet &type=tmp.type();
    result=result && (type.id()==ID_unsignedbv || tmp.id()==ID_signedbv);
  }
  return result;
}


void impara_constrain(
  const exprt &source, 
  exprt &target, 
  const namespacet &ns)
{
  if(source==target)
  {
    target=true_exprt();
  }
  else if(source.id() == ID_and)
  {
    forall_operands(it1, source)
    {
      if(it1->id()==ID_not)
      {
        replace_expr(it1->op0(), false_exprt(), target);
      }
      else if(it1->id()==ID_equal)
      {
        const equal_exprt &equal_expr=to_equal_expr(*it1);
        const exprt &left=equal_expr.op0();
        const exprt &right=equal_expr.op1();
        replace_expr(left, right, target);
      }
      else 
      {
        replace_expr(*it1, true_exprt(), target);
      }
    }
  }
  else
  { 
    if(source.id()==ID_not)
    {
      replace_expr(source.op0(), false_exprt(), target);  
    }
    else if(source.id()==ID_equal)
    {
      const equal_exprt &equal_expr=to_equal_expr(source);
      const exprt &left=equal_expr.op0();
      const exprt &right=equal_expr.op1();
      replace_expr(left, right, target);
    }
    else
    {
      replace_expr(source, true_exprt(), target);
    }
  }
}

void impara_conjoin(
  const exprt &source, 
  exprt &target, 
  const namespacet &ns)
{

  #ifdef DEBUG
  exprt old_target=target;
  #endif

  // remove redundancies
  impara_constrain(source, target, ns);
  exprt src=source; 
  impara_constrain(target, src, ns);

  if(src.is_true())
    return;

  if(target.is_true() || target.is_nil())
    target.swap(src);
  else if(target.id() == ID_and)
    target.move_to_operands(src);
  else
  {
    and_exprt tmp(target, src);
    target.swap(tmp);
  }

  /*
  if(redundancy)
  {
    std::cout << " ==> " << from_expr(target) << std::endl;
  }
  */
}

void impara_disjoin(const exprt &source, exprt &target, const namespacet &ns)
{
  bool redundancy=false;

  #ifdef DEBUG
  exprt old_target=target;
  #endif


  exprt src=source;

  redundancy=!replace_expr(source, false_exprt(), target)||redundancy;
  
  exprt not_src=not_exprt(source);

  simplify(not_src, ns);
  impara_constrain(not_src, target, ns);
    
  redundancy=!replace_expr(target, false_exprt(), src)||redundancy;

  #ifdef DEBUG
  if(redundancy)
  {
    std::cout << " ============ BEFORE " << std::endl;
    std::cout << "    " << from_expr(source) << std::endl;
    std::cout << " || " << from_expr(old_target) << std::endl;
    std::cout << " ============ AFTER " << std::endl;
    std::cout << "    " << from_expr(src) << std::endl;
    std::cout << " || " << from_expr(target) << std::endl;
    std::cout << " ============ " << std::endl;
  }
  #endif



  if(target.is_false() || target.is_nil())
    target.swap(src);
  else if(target.id() == ID_or)
    target.move_to_operands(src);
  else
  {
    or_exprt tmp(target, src);
    target.swap(tmp);
  }
}


/*******************************************************************\

Function: impara_path_searcht::implies

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool implies(const exprt& e1, const exprt& e2, const namespacet &ns) 
{
  // cheap syntactic cover?
  if(e2.is_true() ||
     e1.is_false() ||
     e1==e2)
  {
    return true;
  }
  
  if(e2.is_false() || 
     e1.is_true())
  {
    return false;
  }
    
  // e2 is an and 
  if(e2.id()==ID_and) {
    bool result=true;
  
    forall_operands(it, e2) {
      result=result && implies(e1, *it, ns);
    }
		
    return result;
  }
  else if(e2.id()==ID_or) {
    // go through all operands and try to find e1
    forall_operands(it, e2) {
      if(*it==e1) {
        return true;
      }
    }
  }

  // e1 is a logical and and e2 occurs in e1
  if(e1.id()==ID_and) {
    // go through all operands and try to find e2
    forall_operands(it, e1) {
      if(*it==e2) {
	return true;
      }
    }
  }  

  exprt query = not_exprt(e2);

  //rewrite_arithmetic(query, ns);

  impara_conjoin(e1, query, ns);
  simplify(query, ns);

  return query.is_false();
}


