#include <algorithm>

#include <util/replace_expr.h>
#include <util/i2string.h>

#include "shared_step.h"

#include "nodes.h"

#include "symex/propagation.h"
#include "symex/replace_step.h"

#define DEBUG

#ifdef DEBUG
#include <iostream>
#endif
	 
		 
 
void cone_of_influence(
 	      const locst &locs,
        impara_var_mapt &var_map,  
   	    propagationt &propagation,
  	    node_reft from,
  	    node_reft to,
 	      std::set<exprt>& reads,
  	    std::set<exprt>& writes)
  {  
    std::set<exprt> dummy_reads, dummy_writes;
  
    bool reached_to=false;

    for(impara_step_reft h(from->history); !h.is_nil();--h)
    {
      impara_stept &step=*h;
    
      reached_to=reached_to||step.node_ref==to;

      if(reached_to && step.node_ref!=to) break;
      
      node_reft current_node=step.node_ref;
 
      propagation(h.rename(current_node->label, current_node));
      propagation(h.rename(to->label, current_node));
    }
    
    propagation(from->history.rename(to->label, from));
    propagation(from->history.rename(from->label, from));
	
    reached_to=false;
		
    for(impara_step_reft h(from->history); !reached_to && !h.is_nil();--h)
    {
      impara_stept &step=*h;
    
      reached_to=reached_to||step.node_ref==to;

      shared_stept shared_step(locs,
     	                       var_map, 
	                           step, 
	                           false);

      shared_step(step.node_ref->label, reads); 
      
      if(!step.is_hidden())
      {
  	    shared_step(reads, writes);
        #ifdef DEBUG
        std::cout << "shared step " << step.pretty(var_map.ns, locs, propagation) 
                    << " #writes " << writes.size() << std::endl;
        #endif
      }
    }
		
    //shared_stept shared_step(locs, var_map, *from->history);
    //shared_step(from->label, reads);
  }
  
/*******************************************************************\

Function: sensitivity

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool abstract_commutation(
    const locst &locs,
    impara_var_mapt &var_map,
    node_reft current,
    node_reft ancestor,
    node_reft mover)
{
	const namespacet &ns=var_map.ns;
  
  std::cout << "<<<<<<<<<<<<<<<<<<<<" << std::endl;
  std::cout << "abstract_commutation current " << current->number 
                                               << " ancestor " << ancestor->number 
                                               << " mover " << mover->number << std::endl;
	
  for(; !ancestor.is_nil() && !ancestor->has_label();--ancestor);     
	 
  propagationt prop(ns);
	 
 
  // turn A into a history
  propagationt propagation_mover(
          ns,
          mover->history,
          ancestor);

  propagation_mover.set_hidden(true);

  std::set<exprt> mover_reads, mover_writes;
	

  cone_of_influence(locs, var_map, propagation_mover, mover, ancestor, mover_reads, mover_writes);

  // split B into VCs
  
  propagationt propagation_current(
          ns,
          current->history,
          ancestor);
  
  propagation_current.set_hidden(true);
  
  std::set<exprt> current_reads, current_writes;
  
  cone_of_influence(locs, var_map, propagation_current, current, ancestor, current_reads, current_writes);
  
  
  bool dependence=shared_stept::intersect(current_reads, mover_writes)
               || shared_stept::intersect(current_writes, mover_reads)
               || shared_stept::intersect(current_writes, mover_writes);
  
  
  #ifdef DEBUG
  
  std::cout << "sensitivity checker VCs" << std::endl;
  
  /*
  for(unsigned i=0; i<vcs.size(); ++i)
  { 
  	std::cout << vcs[i].pretty(ns, locs) << std::endl;
  }
  */

  if(dependence)
  {
    std::cout << "Dependent"<<std::endl;
  }
  else
  {
    std::cout << "Independent"<<std::endl;
  }
  shared_stept::output(mover_reads, mover_writes,std::cout);
  shared_stept::output(current_reads, current_writes,std::cout);
	

  
  #endif
  
  return !dependence;


}

/*******************************************************************\

Function: abstract_independencet::pretty

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string abstract_independencet::pretty() const
{
	std::string result;
	
	result+="N"+i2string(current->number)+"/"
				+"N"+i2string(ancestor->number)+"/"
				+"N"+i2string(mover->number);
				
	return result;
}


