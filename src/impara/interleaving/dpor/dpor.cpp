/*******************************************************************\

Module: Forward Path Search with Dynamic Partial Order Reduction

Author: Daniel Kroening, kroening@kroening.com
        Bjorn Wachter, bjoern.wachter@gmail.com
        Subodh Sharma, subodh.sharma@gmail.com
\*******************************************************************/

#include <sstream>
#include <fstream>
#include <algorithm>

#include <util/prefix.h>
#include <util/i2string.h>
#include <util/time_stopping.h>
#include <util/expr_util.h>
#include <util/simplify_expr.h>

#include <solvers/flattening/bv_pointers.h>
#include <solvers/sat/satcheck.h>

#include "symex/from_ssa.h"

#include "../../impara_path_search.h"
#include "../utility/shared_step.h"

#include "happens_before.h"

#include "path_visitor.h"

#include <symex/symex.h>
#include <symex/propagation.h>
#include <symex/impara_symex_replay.h>

#include <symex/build_goto_trace.h>

//#define DEBUG

/*
  [svs]: returns the thread_id of an active thread
  which has not been explored from the state yet and
  is not in the sleep set.
 */
unsigned impara_path_searcht::pick_thread(statet &state)
{
  unsigned result = unsigned(-1);
  unsigned current_thread = state.get_current_thread();

  nodet &node=*state.node_ref;

  if(!state.history.is_nil() 
     && state.history->inside_atomic())
  {   
    if(node.sleep.count(state.history->thread_nr)!=0)
      return -1;
    else   
      return state.history->thread_nr;
  }

  if (state.threads[current_thread].active &&
      node.expanded_threads.count(current_thread) == 0 &&
      node.sleep.count(current_thread) == 0)
  {
    result = current_thread;
  }
  else
  {   
    if (state.atomic_section_count == 0)
    {
      unsigned nr_threads=state.threads.size();
     
      // round-robin scheduling
     
      for (unsigned t = (current_thread+1) % nr_threads; 
           t != current_thread; 
           t=(t+1) % nr_threads)
      {
        if (!state.threads[t].active
         || node.sleep.count(t) != 0
         || node.expanded_threads.count(t) !=0
        ) continue;

        result = t;
        break;
      }
    } 
  }
  
  return result;
}

/*
  Func:    update_sleepset
  Input:   state
  Output:  
  Summary: 
            1) For the argument state, identifies the step leading 
	       to that state
	    2) For that step, identify the node
	    3) If the step conflicts with the entries in the sleep-set 
	       then remove the conflicting threads from the sleep-set. 
	    4) Else, update the argument state's node's sleep-set by 
	       copying the curr-node's sleep-set in to it.
	    5) Finally, update the current-node's sleep-set with the 
	       set that was  executed to reach the argument state.
 */

void impara_path_searcht::update_sleepset(statet & state)
{
  impara_step_reft curr_step (state.history);
 
  if(curr_step.is_nil())
  {
    state.node_ref->sleep.clear();
    return;
  }

  if(curr_step->inside_atomic())
    return;

  unsigned curr_thread = curr_step->thread_nr;  
  node_reft curr_node = curr_step->node_ref;
  
  #ifdef DEBUG
  for(nodet::sleep_sett::iterator 
    	it = state.node_ref->sleep.begin(); 
      it != state.node_ref->sleep.end(); 
      it++)
  {
    impara_step_reft h_step = (*it).second;
    std::cout << "     " << h_step->node_ref->number << std::endl;
    
  }
  #endif

  shared_stept::sett curr_reads, curr_writes;


  for (impara_step_reft history_step=curr_step;
       !history_step.is_nil() 
	     && history_step->node_ref==curr_node;
	     --history_step)
	{
	  shared_stept shared_step(locs, state.var_map, *history_step, do_dpor_pointers);
	  shared_step(curr_reads, curr_writes);
	}
 
  if(curr_reads.empty() && curr_writes.empty())
  {
    for(nodet::sleep_sett::iterator 
    	it = curr_node->sleep.begin(); 
      it != curr_node->sleep.end(); 
      it++)
    {
      impara_step_reft h_step = (*it).second;
    
      if(h_step->thread_nr!=curr_thread)
        state.node_ref->sleep[h_step->thread_nr]=h_step;
    }

    return;
  }
  else
  {
    // find first node where thread was expanded
    // and not in sleep set
    for(node_reft node_ref=curr_node; 
	      !node_ref.is_nil();
	      --node_ref)
    {
      curr_node=node_ref;

      if(node_ref->thread_nr!=curr_thread)
        break;
      if(!node_ref->expanded(curr_thread))
        break;
      if(node_ref->sleep.count(curr_thread))
        break;
    }
  }

  #ifdef DEBUG
  std::cout << "node " << state.node_ref->number 
            << " curr " << curr_node->number << std::endl;

  shared_stept::output(curr_reads, curr_writes, std::cout);
  #endif

  for(nodet::sleep_sett::iterator 
    	it = curr_node->sleep.begin(); 
      it != curr_node->sleep.end(); 
      it++)
  {
    impara_step_reft h_step = (*it).second;
 
    shared_stept::sett h_reads, h_writes;
    shared_stept shared_step(locs, state.var_map, *h_step, do_dpor_pointers);
    shared_step(h_reads, h_writes);

	  #ifdef DEBUG
    std::cout << "Node " << curr_node->number
              << "thread " << h_step->thread_nr << std::endl;
    shared_stept::output(h_reads, h_writes, std::cout);
		#endif


    if(curr_thread !=h_step->thread_nr // thread always has dependency with itself	 
       && !shared_stept::conflict(curr_reads, curr_writes, h_reads, h_writes))
    {
      #ifdef DEBUG   
      std::cout << "Conflict!" << std::endl;
			#endif
      
      state.node_ref->sleep.insert(*it);
    }
  }

  // update the current node's sleep set as well 
  for(node_reft node_ref=curr_step->node_ref; 
      !node_ref.is_nil();
      --node_ref)
  {
   if(node_ref->sleep.count(curr_thread)==0)
     node_ref->sleep[curr_thread]=curr_step;		
   if(node_ref==curr_node)
     break;
  }
  
  return;
}

/*
  Func:    do_backtrack(backtrackt &backtrack)
  Input:   a map of <node_ref, thread_sett> backtrack 
  Output:  bool
  Summary: 
           1) take the reversed backtrack map <node_reft, 
	      thread_sett>
	   2) take the first entry in the map where exists 
	      a thread that is not explored yet from the node
	      or the node is not covered 
           3) Replay to the particular node and take the  
	      untaken action.
           4) The resulting state is put in to the queue
	   5) Repeat this process untill all such backtracking 
	      states are discovered and added to the queue.
*/

bool impara_path_searcht::do_backtrack(backtrackt &backtrack)
{
  backtrackt::reverse_iterator it=backtrack.rbegin();

  unsigned backtracks=0;

  bool result=false;

  // find a suitable backtrack point
  for (; it != backtrack.rend();++it)
  {
    thread_sett threads = it->second;
    node_reft node = it->first;

    for (nodet::thread_sett::const_iterator 
         thread_iterator = threads.begin();
         thread_iterator != threads.end();
         ++thread_iterator)
    {
      unsigned curr_thread = *thread_iterator;

      assert(!node.is_nil());           
     
      // check if the current thread has not already been 
      // expanded from the node
      if (node->expanded(curr_thread))
      {
        continue;
      }

      if(node->is_covered())
      {
        continue;
      }

      statet state(initial_state());

      impara_symex_replay(state, node);

  		state.node_ref->expanded_threads.insert(curr_thread);

      if(!state.is_active(curr_thread))
      {
        continue;
      }
      
      update_sleepset(state);

      queue.push_back(state);
      
      ++backtracks;
      
      succ(curr_thread, queue.back(), queue);
      result=true;
    }
  }

  status() << "do_backtrack: " << backtracks << eom;

  backtrack.clear();

  return result;
}

void null_predicate_rec(const namespacet &ns,
                        const statet &state,
                        const exprt &lhs, 
                        const exprt &value,
                        std::vector<exprt>& result)
{
  const typet &type=lhs.type();
 
  const typet &lhs_type=ns.follow(lhs.type());
  const typet &value_type=ns.follow(value.type());

  if(value.is_nil())
  {
    return;
  }
  
  // is this a pointer?
  if(lhs_type.id()==ID_pointer)
  {
    exprt is_null(equal_exprt(from_ssa(lhs), gen_zero(type)));
  
    if(state.is_null(value))
    {
      result.push_back(is_null);
    }
    else
    {
      result.push_back(not_exprt(is_null));
    }
  } else if(lhs_type.id()==ID_struct)
  {

    if(value_type!=lhs_type)
      return;

    const struct_typet &struct_type=to_struct_type(lhs_type);
    const struct_typet::componentst &components=struct_type.components();

    if(value.operands().size() < components.size())
      return;

    // split it up into components
    for(unsigned i=0; i<components.size(); i++)
    {
      const typet &subtype=components[i].type();
      const irep_idt &component_name=components[i].get_name();

      exprt new_lhs=member_exprt(lhs, component_name, subtype);

      null_predicate_rec(ns,
                         state,
                         new_lhs, 
                         value.operands()[i], 
                         result);
    }   
  }
}


exprt null_predicate(const namespacet &ns, 
                     const statet &state)
{

  std::vector<exprt> result;
   
  
  // shared variables
  for(statet::var_valt::const_iterator 
      it=state.shared_vars.begin();
      it!=state.shared_vars.end();
      ++it)
  {
    const statet::var_statet &var_state=*it;

    null_predicate_rec(ns, state, var_state.ssa_symbol, var_state.value, result);
  }
  
  // thread-local variables
  for(statet::threadst::const_iterator
      thread_it=state.threads.begin();
      thread_it!=state.threads.end();
      ++thread_it)
  {
    const statet::var_valt &var_val=thread_it->local_vars;
    
     for(statet::var_valt::const_iterator 
         it=var_val.begin();
         it!=var_val.end();
         ++it)
    {
      const statet::var_statet &var_state=*it;  

      null_predicate_rec(ns, state, var_state.ssa_symbol, var_state.value, result);
    } 
  }

  return conjunction(result);
}


void impara_path_searcht::dpor_search()
{
  status() << "Starting search with DPOR" << eom;


  /* configuration */
  do_dpor_pointers=options.get_bool_option("dpor-pointers");
  do_refine_close=false;

  status() << (do_dpor_pointers ? "Abstract dependency relation for pointers" : 
                                  "Read-write-set dependencies") << eom;  

  backtrackt backtrack;
  
  dpor_path_visitort visitor(locs, var_map, backtrack, do_dpor_pointers); 

  // 1) push initial state in the queue.
  queue.push_back(initial_state());

  initial_node_ref = queue.back().node_ref;

  unsigned report_interval=1000;


  // 2) Iterate while there are enabled processes from the
  // state that are not in the sleep set.

  while (true)
  {
    #ifdef DEBUG
    //print_queue(queue);
    #endif

    // 3) choose a state
    queuet::iterator state_iterator = select_state(queue);

    statet &curr_state = *state_iterator;

    if (state_iterator == queue.end())
    {
      status() << "Backtrack size " << backtrack.size() << eom;
    
      if(do_backtrack(backtrack))
      {
        
      	continue;
      }
      else
      {
      	return;
      }	
    }

    if(drop_state(curr_state))
    {    
      curr_state.node_ref->refine(ns, merge, refinements, false_exprt());
      forall_prefixes(curr_state.node_ref, visitor);
      queue.erase(state_iterator);
      continue;
    }
    
    if(curr_state.node_ref->has_label())
    {
      exprt nullness=null_predicate(ns, curr_state);

      curr_state.node_ref->refine(ns, merge, 0, nullness);
    }

    unsigned curr_thread = pick_thread(curr_state);

    // update the sleep set of the state
    update_sleepset(curr_state);
    
    // 4) If no enabled transition, remove the state
    if (curr_thread == unsigned(-1))
    {
      #ifdef DEBUG
      status() << "No thread enabled " << curr_state.node_ref->number << eom;
      #endif
      forall_prefixes(curr_state.node_ref, visitor);
      queue.erase(state_iterator);
      continue;
    }

    else
    {
      if(curr_state.node_ref->number % report_interval == 0)
      {
        status() << "Processing state " << curr_state.node_ref->number << " thread " << curr_thread << eom;
      }

      curr_state.set_current_thread(curr_thread);

      if(ancestor_close(curr_state.node_ref, true))
      {
        #ifdef DEBUG
        status() << "Subsumption: current thread " << curr_state.get_current_thread() << eom;
        status() << "   " << curr_state.node_ref->sleep.count(curr_state.get_current_thread()) << eom;
        #endif
        
        curr_state.node_ref->sleep[curr_state.get_current_thread()]=curr_state.history;
      
        forall_prefixes(curr_state.node_ref, visitor);  

        curr_thread = pick_thread(curr_state);
        
        if (curr_thread == unsigned(-1))
        {
          #ifdef DEBUG
          status() << "No thread enabled " << curr_state.node_ref->number << eom;
          #endif
          forall_prefixes(curr_state.node_ref, visitor);
          queue.erase(state_iterator);
          continue;
        }    
      }
      // record current thread has been expanded
      curr_state.node_ref->expanded_threads.insert(curr_thread);

      // successor states
      queuet successors;     
      successors.splice(successors.end(),queue,state_iterator);

      // execute curr_thread
      if(succ(curr_thread, curr_state, successors))
      {
				queue.splice(queue.end(), successors);

        // refinement just happended
        if(!pruned_node_ref.is_nil())
        {
          forall_prefixes(pruned_node_ref, visitor);
	  			pruned_node_ref.make_nil();
        }
      }
      else
      {
        queue.splice(queue.end(), successors);
      
        forall_prefixes(curr_state.node_ref, visitor);
        continue;
      }
    }
  }
}

/*
void impara_path_searcht::dpor_search()
{
  status() << "Starting search with DPOR" << eom;

  backtrackt backtrack;
 
  dpor_path_visitort visitor(locs, var_map, backtrack); 

  // 1) push initial state in the queue.
  queue.push_back(initial_state());

  initial_node_ref = queue.back().node_ref;

  // 2) Iterate while there are enabled processes from the
  // state that are not in the sleep set.

  while (true)
  {
    #ifdef DEBUG
    //print_queue(queue);
    #endif

    // 3) choose a state
    queuet::iterator state_iterator = select_state(queue);

    statet &curr_state = *state_iterator;

    if (state_iterator == queue.end())
    {
      status() << "Backtrack size " << backtrack.size() << eom;
    
      if(do_backtrack(backtrack))
      {
        
      	continue;
      }
      else
      {
      	return;
      }	
    }
    
    // drop the state if any of the set limits are 
    // reached
    if(drop_state(curr_state))
    {    
      curr_state.node_ref->refine(ns, merge, refinements, false_exprt());
    
      forall_prefixes(curr_state.node_ref, visitor);
       
      queue.erase(state_iterator);
      continue;
    }

    {
      exprt nullness=null_predicate(ns, curr_state);

      curr_state.node_ref->refine(ns, merge, 0, nullness);
    }

    unsigned curr_thread = pick_thread(curr_state);

    // update the sleep set of the state
    update_sleepset(curr_state);
    
    // 4) If no enabled transition, remove the state
    if (curr_thread == unsigned(-1))
    {
      #ifdef DEBUG
      status() << "No thread enabled " << curr_state.node_ref->number << eom;
      #endif
      forall_prefixes(curr_state.node_ref, visitor);
      queue.erase(state_iterator);
      continue;
    }

    else
    {
      if(covered(curr_state))
      {
        forall_prefixes(curr_state.node_ref, visitor);
        continue;
      }
      // record current thread has been expanded
      curr_state.node_ref->expanded_threads.insert(curr_thread);

      // successor states
      queuet successors;     
      successors.splice(successors.end(),queue,state_iterator);

      // execute curr_thread
      if(succ(curr_thread, curr_state, successors))
      {
				queue.splice(queue.end(), successors);

        // refinement just happended
        if(!pruned_node_ref.is_nil())
        {
          forall_prefixes(pruned_node_ref, visitor);
	  			pruned_node_ref.make_nil();
        }
      }
      else
      {
        forall_prefixes(curr_state.node_ref, visitor);
        continue;
      }
    }
  }
}
*/
