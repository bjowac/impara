/*******************************************************************\

Module: Interpolator based on weakest precondition

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/expr_util.h>
#include <util/simplify_expr.h>
#include <util/replace_expr.h>


#include <impara_solver.h>


#include "symex/from_ssa.h"


//#include "wordlevel_interpolator.h"

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
  // weakest preconditions
  
  exprt wp=cond;

  itp_map[node_ref]=from_ssa(wp);

  for(impara_step_reft h(history); !h.is_nil() && h->node_ref!=ancestor; --h)
  {
    const impara_stept &step=*h;

    node_ref=step.node_ref;
   
    wp=step_wp(step, wp, ns);

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






