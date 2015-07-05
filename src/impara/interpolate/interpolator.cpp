/*******************************************************************\

Module: Interpolator based on weakest precondition

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/expr_util.h>
#include <util/simplify_expr.h>
#include <util/replace_expr.h>


#include <impara_solver.h>


#include "symex/from_ssa.h"


#include "wordlevel_interpolator.h"

#include "step_wp.h"
#include "interpolator.h"

//#define DEBUG



#ifdef DEBUG
#include <iostream>
#endif


/*******************************************************************\

Function: wp_interpolatort::operator()

  Inputs: a state, a node ancestor, start and end end condition
 
 Outputs: 

 Purpose: compute path interpolant (for path prefix starting at ancestor)

\*******************************************************************/

decision_proceduret::resultt wp_interpolatort::operator()
(
    impara_step_reft history,
    node_reft node_ref,
    node_reft ancestor,
    const exprt& start,
    const exprt& cond,
    interpolatort::interpolant_mapt& itp_map
)
{


  bool reached_ancestor=false;

  if(do_wordlevel)
  {
    transitivity_interpolatort interpolator(ns);

    node_reft current=history->node_ref;

    for(impara_step_reft h(history); !h.is_nil() && !reached_ancestor; --h)
    {

      const impara_stept &step=*h;

      node_ref=step.node_ref;



      reached_ancestor=reached_ancestor||node_ref==ancestor;

      if(step.guard.is_not_nil() && !step.is_hidden())
        interpolator.add_formula(step.guard, current->number);
        
      if(step.full_lhs.is_not_nil())
      {
        exprt equal=equal_exprt(step.ssa_lhs, step.ssa_rhs);
      
        interpolator.add_formula(equal, current->number);
      }
      
      if(node_ref->has_label())
      {
        current=node_ref;
      }
    }
    
    decision_proceduret::resultt 
      interpolator_result=interpolator.infer();
    
    if (interpolator_result==decision_proceduret::D_UNSATISFIABLE)
    {
    
      reached_ancestor=false;

      for(impara_step_reft h(history); !h.is_nil() && !reached_ancestor; --h)
      {

        const impara_stept &step=*h;

        node_ref=step.node_ref;

        reached_ancestor=reached_ancestor||node_ref==ancestor;

        exprt interpol;

        interpolator.get_interpolant(step.node_ref->number, interpol);

        if(node_ref->has_label())
        {
          simplify_expr(interpol, ns);
          itp_map[node_ref]=interpol; 
        }
      }
      
      return interpolator_result; 
    }
  }

  // weakest preconditions
  
  exprt wp=cond;

  reached_ancestor=false;

  bool forall_itp=options.get_bool_option("forall-itp");

  itp_map[node_ref]=from_ssa(wp);

  for(impara_step_reft h(history); !h.is_nil() && !reached_ancestor; --h)
  {
    const impara_stept &step=*h;

    node_ref=step.node_ref;

    reached_ancestor=reached_ancestor||node_ref==ancestor;
    
    wp=step_wp(step, wp, forall_itp, ns);

    exprt label=from_ssa(wp);

    simplify(label, ns);

    if(label.is_true()) {
      break;
    }

    if(node_ref->has_label())
    {
      itp_map[node_ref]=label; 
    }
  }


  return decision_proceduret::D_UNSATISFIABLE;
}






