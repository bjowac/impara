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

  if(do_wordlevel)
  {
    std::set<unsigned> seen;
    std::map<unsigned, unsigned> partition;
    unsigned partitions=0;

    for(impara_step_reft h(history); !h.is_nil() && h->node_ref!=ancestor ; --h)
    {

      const impara_stept &step=*h;

      if(step.node_ref->has_label())
      {
        if(seen.count(step.node_ref->number)==0)
        {
          ++partitions;
          seen.insert(step.node_ref->number); 
        }
      }
    }

    partition[ancestor->number]=0;
    partition[node_ref->number]=partitions+1;


    
    
    std::vector<std::pair<exprt, unsigned> > formulas;

    formulas.push_back(std::make_pair(start, 0));
    formulas.push_back(std::make_pair(not_exprt(cond), partitions));

    for(impara_step_reft h(history); !h.is_nil() && h->node_ref!=ancestor; --h)
    {

      const impara_stept &step=*h;

      if(step.node_ref->has_label())
      {
        if(partition.find(step.node_ref->number)==partition.end())
          partition[step.node_ref->number]=partitions--;
      }
      else
      {
        partition[step.node_ref->number]=partitions;
      }
    }
    
    std::cout << "(VCC) " << partition[node_ref->number] 
      << " " << from_expr(ns, "", not_exprt(cond)) << std::endl;

    for(impara_step_reft h(history); !h.is_nil() && h->node_ref!=ancestor; --h)
    {

      const impara_stept &step=*h;

      if(step.guard.is_not_nil() && !step.is_hidden())
      {
        std::cout << "(G) " << partition[step.node_ref->number] << " " << from_expr(ns, "", step.guard) << std::endl;
        exprt guard(step.guard);

        simplify_expr(guard, ns);

        formulas.push_back(std::make_pair(guard, partition[step.node_ref->number]));
      } 
        
      if(step.full_lhs.is_not_nil())
      {
      
        if(step.ssa_rhs.is_not_nil())
        {
      
          exprt equal=equal_exprt(step.ssa_lhs, step.ssa_rhs);
      
          std::cout << "(E) " << partition[step.node_ref->number] << " " << from_expr(ns, "", equal) << std::endl;
      
          formulas.push_back(std::make_pair(equal, partition[step.node_ref->number]));
          
        }
      }
    }


    std::cout << "(A) " << partition[ancestor->number] << " " << from_expr(ns, "", start) << std::endl;
    
    transitivity_interpolatort interpolator(ns);

    for(std::vector<std::pair<exprt, unsigned> >::iterator
        it=formulas.begin(); it!=formulas.end(); ++it)
    {
      interpolator.add_formula(it->first, it->second);
    }

    decision_proceduret::resultt 
      interpolator_result=interpolator.infer();




    expr_listt interpolants;

    interpolator.get_interpolants(interpolants);
      
    for (expr_listt::const_iterator e_it=interpolants.begin();
         e_it!=interpolants.end(); e_it++)
    {
      std::cout << from_expr(ns, "", *e_it) << std::endl;
    }


    
    if (interpolator_result==decision_proceduret::D_UNSATISFIABLE)
    {
      for(node_reft n(node_ref); !n.is_nil(); --n)
      {
        exprt interpol;

        interpolator.get_interpolant(partition[n->number], interpol);

        if(n->has_label() || n==ancestor)
        {
          simplify_expr(interpol, ns);
          
          std::cout << "Interpolant " << partition[n->number] << " N" << 
            n->number << " : " << from_expr(ns, "", interpol) << std::endl;
          
          itp_map[n]=interpol; 
        }

        if(n==ancestor)
          break;
      }
      
      return interpolator_result; 
    }
  }

  // weakest preconditions
  
  exprt wp=cond;

  bool forall_itp=options.get_bool_option("forall-itp");

  itp_map[node_ref]=from_ssa(wp);

  for(impara_step_reft h(history); !h.is_nil() && h->node_ref!=ancestor; --h)
  {
    const impara_stept &step=*h;

    node_ref=step.node_ref;
   
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






