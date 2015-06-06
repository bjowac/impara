/*******************************************************************\

Module: Interval-based VCC checker
 
Author: Bjorn Wachter, bjoern.wachter@cs.ox.ac.uk

\*******************************************************************/

#include <algorithm>

#include <util/arith_tools.h>
#include <util/expr_util.h>
#include <util/decision_procedure.h>
#include <util/i2string.h>
#include <util/find_symbols.h>

#include <ansi-c/c_types.h>


#include "impara_join.h"
#include "interval_checker.h"

//#define DEBUG

#include <iostream>

/*******************************************************************\

Function: interval_checkert::operator()

  Inputs: 

 Outputs: 

 Purpose:

\*******************************************************************/


decision_proceduret::resultt interval_checkert::operator()
(
  impara_step_reft history,
  node_reft node_ref,
  node_reft ancestor,
  const exprt& start,
  const exprt& cond,
  interpolant_mapt& itp_map)
{
  decision_proceduret::resultt result=decision_proceduret::D_ERROR;

  find_symbols(start,depends);
  find_symbols(cond,depends);

  relevant_assignments();

  std::vector<impara_step_reft> steps;

  bool reached_ancestor=false;

  for(impara_step_reft h(history); !h.is_nil(); --h)
  {
    const impara_stept &step=*h;

    reached_ancestor=reached_ancestor||step.node_ref==ancestor;

    if(reached_ancestor && step.node_ref!=ancestor) continue;

    steps.push_back(h);
  } 

  std::reverse(steps.begin(), steps.end());

  for(unsigned i=0; i<steps.size(); ++i)
  {
    const impara_stept &step=*steps[i];

    if(!step.ssa_lhs.is_nil())
    {
      interval_dom.assign(step.ssa_lhs, step.ssa_rhs);
    }

    if(!step.guard.is_nil())
    {
      interval_dom.assume_rec(step.guard);
    }

    node_reft node_ref=step.node_ref;

    if(node_ref->has_label())
    {
      // TODO
      itp_map[node_ref]=true_exprt();
    }
  }

  interval_dom.output(ns, std::cout);  

  std::cout << "Result " << from_expr(cond)<<std::endl;
  std::cout << " ====> " << interval_dom.eval(cond) << std::endl;


  return result;
}

void interval_checkert::relevant_assignments()
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
