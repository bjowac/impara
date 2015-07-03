/*******************************************************************\

Module: Slice history w.r.t. a verification condition

Author: Bjorn Wachter, bjoern.wachter@cs.ox.ac.uk

\*******************************************************************/

#include <limits>

#include <util/arith_tools.h>
#include <util/expr_util.h>
#include <util/decision_procedure.h>
#include <util/i2string.h>
#include <util/find_symbols.h>

#include <ansi-c/c_types.h>


#include "impara_join.h"
#include "simple_checker.h"

#define DEBUG

#ifdef DEBUG
#include <iostream>
#endif

/*******************************************************************\

Function: simple_checkert::set_hidden

  Inputs: 

 Outputs: 

 Purpose:

\*******************************************************************/




decision_proceduret::resultt 
simple_checkert::operator()(const exprt& start, const exprt& cond) 
{
  decision_proceduret::resultt 
    result=decision_proceduret::D_ERROR;

  find_symbols(start,depends);
  find_symbols(cond,depends);

  propagation.set_hidden(true);

  exprt condition=propagation(cond);
  
  bool unknown_branch=false;
  
  impara_step_reft infeasible_step;
  
  if(implies(start, condition, ns))
  {
    result=decision_proceduret::D_UNSATISFIABLE;   
    return result;
  }
  else 
  {
    bool reached_ancestor=false;

    unsigned minimal_cost=std::numeric_limits<unsigned>::max();

    for(impara_step_reft h(history); !h.is_nil(); --h)
    {
      impara_stept& step=*h;
      
      reached_ancestor=reached_ancestor||step.node_ref==ancestor;

      if(reached_ancestor && step.node_ref!=ancestor) break;
      
      if(step.guard.is_not_nil()) 
      {
        unsigned cost=0;
      
        exprt guard=propagation(step.guard, cost);
        
        if(guard.is_false())
        {        
          if(minimal_cost > cost)       
          {
            infeasible_step=h;
            minimal_cost=cost;
          }
        } 
        else if(guard.is_true())
        {
          // continue
        }
        else
        {
          unknown_branch=true;
        }
      }    
    }
    
    if(!infeasible_step.is_nil())
    {
      propagation.set_hidden(true);
      propagation(infeasible_step->guard);
    
      infeasible_step->set_hidden(false);
      return result=decision_proceduret::D_UNSATISFIABLE;    
    } else if(!unknown_branch && condition.is_false())
    {
      return decision_proceduret::D_SATISFIABLE;
    }
  }
  
  // set only the guards to visible again
  for(impara_step_reft h(history); !h.is_nil(); --h)
  {
    impara_stept &step=*h;
    
    if(step.guard.is_nil())
      continue;
      
    find_symbols(step.guard, depends);
    step.reset_hidden();
  }
  
  // put in all relevant symbols
  relevant_assignments();
  
  return result;
}

void simple_checkert::relevant_assignments()
{
  bool reached_ancestor=false;

  for(impara_step_reft h(history); !h.is_nil(); --h)
  {
    impara_stept &step=*h;

    reached_ancestor=reached_ancestor||step.node_ref==ancestor;

    if(reached_ancestor && step.node_ref!=ancestor) continue;

    if(step.full_lhs.is_not_nil())
    { 
      if(depends.find(step.ssa_lhs.get_identifier())==depends.end())
      {        
      }
      else
      {
        find_symbols(step.ssa_rhs,depends);
        step.set_hidden(false);
      }
    }
  }
}
