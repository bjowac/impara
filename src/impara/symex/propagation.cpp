/*******************************************************************\

Module: propagation

Author: Bjorn Wachter, bjoern.wachter@cs.ox.ac.uk

\*******************************************************************/
#include <util/simplify_expr.h>
#include <util/arith_tools.h>
#include <util/expr_util.h>
#include <util/decision_procedure.h>
#include <util/find_symbols.h>
#include <util/base_type.h>

#include <ansi-c/c_types.h>

#include "from_ssa.h"

#include "simple_checker.h"

//#define DEBUG

#ifdef DEBUG
#include <iostream>
#endif

/*******************************************************************\

Function: propagationt::replace_rec

  Inputs: 

 Outputs: 

 Purpose: apply in-place replacement of propagated symbols to dest

\*******************************************************************/

bool propagationt::replace_rec(exprt &dest, unsigned &cost)
{
  bool change=false;


  cachet::const_iterator cache_it=cache.find(dest);      
 
  if(cache_it!=cache.end())
  {
    const cache_entryt &entry=cache_it->second;
    dest=entry.first;
    cost+=entry.second;
    change=true;
  } 
  else 
  if(dest.id()==ID_symbol )
  {
    defst::const_iterator defs_it=defs.find(dest);
  
    if(defs_it==defs.end())
    {
      change=false;
    }
    else
    {
      const valuet& v=defs_it->second;
      
      cost+=v.cost;
     
      if(!v.step.is_nil())
      {
        v.step->set_hidden(false);
      }      

      exprt tmp(v.value);
     
      replace_rec(tmp, cost);
      
      cache_entryt entry(tmp, cost);
      
      cache.insert(std::pair<exprt, cache_entryt>(dest, entry));
      dest.swap(tmp);
      change=true;
    }
  }
  
  if(dest.has_operands())
  {
  
    Forall_operands(it, dest)
    {
      change=replace_rec(*it, cost)||change;
    }
    
    if(change)
    {
      simplify(dest, ns);  
    }
  }

  return change;
}


propagationt::propagationt(
              const namespacet &__ns
)
: ns(__ns)
{
}

propagationt::propagationt(
              const namespacet &__ns,
              impara_step_reft& __history,
              node_reft __ancestor)
: ns(__ns), history(__history), ancestor(__ancestor)
{
  bool reached_ancestor=false;
 
  for(impara_step_reft h(history); !h.is_nil(); --h)
  {
    impara_stept& step=*h;

    reached_ancestor=reached_ancestor||step.node_ref==ancestor;

    if(reached_ancestor && step.node_ref!=ancestor) break;

    *this << h; 
  }
}


propagationt& propagationt::operator<<(const impara_step_reft &step_ref)
{
  impara_stept& step=*step_ref;
  
  if(step.guard.is_not_nil())
  {
    //§§assume(step.guard);
  }
 
  if(step.full_lhs.is_not_nil() && step.ssa_rhs.is_not_nil()) 
  {
    defs.insert(std::pair<exprt, valuet>(step.ssa_lhs, step_ref));
  }
  
  return *this;
}

void propagationt::assume_equality(const exprt &src)
{
  if(src.id()==ID_equal)
  {
    const exprt &op0=src.op0();
    const exprt &op1=src.op1();

    if(op0.id()==ID_symbol && defs.find(op0)==defs.end())
    {   
      defs.insert(std::pair<exprt, valuet>(op0, op1));
    }
    else if(op1.id()==ID_symbol && defs.find(op1)==defs.end())
    {   
      defs.insert(std::pair<exprt, valuet>(op1, op0));
    }
  }
  else if(src.id()==ID_not)
  {
    const exprt false_expr=false_exprt();
    const exprt true_expr=true_exprt();
    cache.insert(std::pair<exprt, cache_entryt>(src.op0(), cache_entryt(false_expr,0)));
    cache.insert(std::pair<exprt, cache_entryt>(src, cache_entryt(true_expr,0)));
  }
  else
  {
    const exprt true_expr=true_exprt();
    cache.insert(std::pair<exprt, cache_entryt>(src, cache_entryt(true_expr,0)));
  }
}

void propagationt::assume(const exprt &src)
{
  if(src.id()==ID_and)
  {
    forall_operands(it, src)
    {
      assume_equality(*it);
    }
  }
  else
  {
    assume_equality(src);
  }

}


exprt propagationt::operator()(const exprt &dest, bool from_cache)
{
  unsigned cost=0;
  return operator()(dest, cost, from_cache);
}

exprt propagationt::operator()(const exprt &dest, unsigned &cost, bool from_cache)
{
  if(from_cache)
  {
    cachet::const_iterator cache_it=cache.find(dest);    
  
    if(cache_it!=cache.end())
    {
      const cache_entryt &entry=cache_it->second;
      cost=entry.second;
    
      return entry.first;
    }
    else
    {
      return dest;
    }
  }

  exprt tmp(dest);
  replace_rec(tmp, cost);
  simplify(tmp, ns);
  
  return tmp;
}


void propagationt::set_hidden(bool value, bool guards_only) 
{
  if(value)
    cache.clear();

  bool reached_ancestor=false;

  for(impara_step_reft h(history); !h.is_nil(); --h)
  {
    impara_stept &step=*h;
    
    reached_ancestor=reached_ancestor||step.node_ref==ancestor;

    if(reached_ancestor && step.node_ref!=ancestor) break;
      
    if(guards_only && step.guard.is_nil())
      continue;
      
    step.set_hidden(value);
  }
}

unsigned compute_cost(const impara_step_reft &step)
{
  /* cost measure:
     penalty for incremental updates 
   */
  
  exprt lhs=from_ssa(step->ssa_lhs);
  exprt rhs=from_ssa(step->ssa_rhs);
  
  if(lhs.is_nil())
    return 0;
    
  if(rhs.is_nil())
    return 0;
  
  find_symbols_sett symbols;
  
  find_symbols(rhs, symbols);

  bool incremental=symbols.find(to_symbol_expr(lhs).get_identifier())!=symbols.end();
  
  if(incremental)
    return 1;
  else
    return 0;
}

propagationt::valuet::valuet(const impara_step_reft &_step)
    : step(_step), 
      value(step->ssa_rhs),
      cost(compute_cost(_step))
    {}
  
propagationt::valuet::valuet(const exprt &_value)
    : value(_value), cost(0) 
    {}


