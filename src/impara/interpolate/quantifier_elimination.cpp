#include <util/replace_expr.h>
#include <util/simplify_expr.h>
#include <util/find_symbols.h>

#include "impara_solver.h"

#include <impara_join.h>

#include "quantifier_elimination.h"

//#define DEBUG

#include <iostream>
#include <langapi/language_util.h>


/*******************************************************************\

Function: has_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool has_symbol(const symbol_exprt &s, const exprt &where)
{
  if(where.id()==ID_symbol)
    return s.get_identifier()==to_symbol_expr(where).get_identifier();

  forall_operands(it, where)
    if(has_symbol(s, *it)) return true;

  return false;
}




/*******************************************************************\

Function: split_overflow

  Inputs: 

 Outputs: 

 Purpose: splits disjunction of constraints into ordinary 
          and overflow constraints

\*******************************************************************/

void split_overflow(
  const exprt &src,
  exprt &other,
  exprt::operandst &overflow)
{
  exprt::operandst phi_sub;

  if(src.id()==ID_or)
  {
    exprt::operandst other_subs;
  
    forall_operands(it, src)
    {
      const exprt &sub=*it;
    
      if(sub.id()==ID_overflow_minus 
      || sub.id()==ID_overflow_plus
      || sub.id()==ID_overflow_mult)
      {
        overflow.push_back(sub);
      }
      else
      {
        other_subs.push_back(sub);
      }
    }
    
    other=disjunction(other_subs);
  }
  else
  {
    other=src;
  }
}


/*******************************************************************\

Function: syntactic_elimination

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void syntactic_elimination(const symbol_exprt &quantifier,
                 exprt &dest,
                 const namespacet &ns)
{
  #ifdef DEBUG
  std::cout << "syntactic_elimination: "
      << from_expr(ns, "", dest) << std::endl;
  #endif

  // This approximates \forall quantifier. dest

  if(dest.id()==ID_or)
  {
    // In case x does not occur in 'B' the following holds:
    // \forall x. (A || B) <---> (\forall x. A) || B

    unsigned count=0;
    forall_operands(it, dest)
      if(has_symbol(quantifier, *it))
        count++;

    if(count==1)
    {
      // yes, special case
      Forall_operands(it, dest)
        if(has_symbol(quantifier, *it))
          syntactic_elimination(quantifier, *it, ns);
    }
  }
  else if(dest.id()==ID_and)
  {
    // \forall x. A && B  <---> (\forall x. A) && (\forall x. B)
    Forall_operands(it, dest)
      syntactic_elimination(quantifier, *it, ns);
  }
  else if(dest.id()==ID_equal || dest.id()==ID_notequal ||
          dest.id()==ID_gt || dest.id()==ID_lt ||
          dest.id()==ID_ge || dest.id()==ID_le)
  {
    // "\forall x. x REL const" is false for any non-singleton x
    assert(dest.operands().size()==2);

    if((dest.op0()==quantifier && dest.op1().is_constant()) ||
       (dest.op1()==quantifier && dest.op0().is_constant()))
    {
      dest.make_false();
    }

  }
  else if(dest.id()==ID_not)
  {
    const exprt &op=dest.op0();

    if(op.id()==ID_equal || op.id()==ID_notequal ||
       op.id()==ID_gt || op.id()==ID_lt ||
       op.id()==ID_ge || op.id()==ID_le)
    {
      // "\forall x. x REL const" is false for any non-singleton x
      assert(op.operands().size()==2);

      if((op.op0()==quantifier && op.op1().is_constant()) ||
         (op.op1()==quantifier && op.op0().is_constant()))
      {
        dest.make_false();
      }
    }
  }
  else if(dest.id()==ID_typecast)
  {
    syntactic_elimination(quantifier, dest.op0(), ns);
  }
}


exprt semantic_elimination(
    const symbol_exprt &quantifier,
    const exprt &src,
    const namespacet &ns)
{
  exprt dest=true_exprt();

  impara_solver_no_simplifiert solver(ns);

  exprt core;
  exprt::operandst overflow;

  split_overflow(
    src,
    core,
    overflow);

  simplify(core, ns);

  #ifdef DEBUG
  std::cout << "Eliminating quantifier "
            << from_expr(ns, "", quantifier)
            << " in "
            << from_expr(ns, "", src) << std::endl
            << "  => " << from_expr(ns, "", core) << std::endl;

  #endif


  std::set<exprt> symbols;
  find_symbols(core, symbols);

  std::vector<exprt> instantiations;

  for(std::set<exprt>::const_iterator 
   it=symbols.begin(); 
   it!=symbols.end(); 
   ++it)
  {
    exprt val=*it;

    // filter
    if(val==quantifier)
      continue;

    if(val.type().id()!=ID_signedbv && val.type().id()!=ID_unsignedbv)
      continue;

    // adapt type of symbol
    if(val.type()!=quantifier.type())
    {
      val=typecast_exprt(val, quantifier.type());
    }


    if(val.type().id()==ID_signedbv)
      instantiations.push_back(unary_minus_exprt(val));

    instantiations.push_back(val);

  }

  // implicit instantiation
  
 
  std::vector<exprt> instances;
  std::vector<literalt> instance_literals;

  for(unsigned i=0; i<instantiations.size();++i)
  {
    exprt val=instantiations[i];
    exprt instance=core;
    replace_expr(quantifier, val, instance);

    simplify(instance, ns);
    instances.push_back(instance);
    instance_literals.push_back(solver(instance));
    if(!instance_literals.back().is_constant())
      solver.set_frozen(instance_literals.back());

    #ifdef DEBUG
    std::cout << "   " << from_expr(ns, "", val)
              << " : " << val.type() << " "
              << from_expr(ns, "", instance) << std::endl;
    #endif
  }

  solver.set_to(core, false);

  std::vector<impara_solvert::contextt> contexts;

  for(unsigned i=0; i<instances.size(); ++i)
  {
    if(solver.dec_solve()==decision_proceduret::D_UNSATISFIABLE)
      break;

    /*
    impara_solvert::contextt context=solver.new_context();
    contexts.push_back(context);
    solver.set_to_context(context, literal_exprt(instance_literals[i]), true);
     */
     
    solver.set_to_true(literal_exprt(instance_literals[i]));
    impara_conjoin(instances[i], dest, ns);
  }

  #ifdef DEBUG
  if(solver.dec_solve()==decision_proceduret::D_SATISFIABLE)
  {
    std::cout << "Warning incomplete QE" << std::endl;
  }
  #endif

  // falling back to explicit instantiation

  unsigned counter=0;

  #if 1
  while(counter < 2 && solver.dec_solve()==decision_proceduret::D_SATISFIABLE)
  {

    // get a model of quantifier
    exprt val=solver.get(quantifier);

    #ifdef DEBUG
    std::cout << "  value " << from_expr(ns, "", val)
              << std::endl;
    #endif

    exprt instance=core;
    replace_expr(quantifier, val, instance);




    #ifdef DEBUG
    std::cout << "F[x:=x] "  
              << " = "
              << from_expr(ns, "", instance) << std::endl;
    #endif

    #if 0
    impara_solvert solver2(ns);

    solver2.set_to(instance, false);

    if(solver2.dec_solve()==decision_proceduret::D_UNSATISFIABLE)
    {
      std::cout << "TAUTOLOGY " << std::endl;
    } else
    {
      std::set<exprt> symbols;
      find_symbols(instance, symbols);
      for(std::set<exprt>::const_iterator 
       it=symbols.begin(); 
       it!=symbols.end(); 
       ++it)
      {
        std::cout << "   " << from_expr(ns, "", *it)
                  << " := " << from_expr(ns, "", solver2.get(*it)) << std::endl;
      }
    }
    #endif
   
    literalt instance_literal(solver(instance));
  
    solver.set_to_true(instance);
    impara_conjoin(instance, dest, ns);

    ++counter;
  }
  #endif

  return dest;
}


/*******************************************************************\

Function: eliminate_forall

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt eliminate_forall(
  const symbol_exprt &quantifier,
  const exprt &src,
  const namespacet &ns)
{
  if(src.id()==ID_and)
  {
    exprt dest=src;

    // \forall x. A && B  <---> (\forall x. A) && (\forall x. B)
    Forall_operands(it, dest)
      eliminate_forall(quantifier, *it, ns);

    return dest;
  }

  exprt src2=src;

  exprt dest=true_exprt();

  syntactic_elimination(quantifier, src2, ns);


  // try syntactic criteria
  if(!has_symbol(quantifier, src2))
  {
    #ifdef DEBUG
    std::cout << "Successful syntactic QE" << std::endl;
    #endif

    dest=src2;
  }
  else
  {
    dest=semantic_elimination(
      quantifier,
      src2,
      ns);
  }

  simplify(dest, ns);

  #ifdef DEBUG
  std::cout << "Eliminated quantifier " << from_expr(ns, "", dest) << std::endl;
  #endif

  return dest;
}


