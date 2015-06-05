#include <iostream>
#include <set>


#include <util/i2string.h>
#include <util/std_expr.h>

#include <path-symex/locs.h>
#include <path-symex/loc_ref.h>


#include "../utility/sensitivity.h"

#include "partial_order_reduction.h"

//#define DEBUG
#define OPTI


/*******************************************************************\

Function: shared_accesst::shared_accesst

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
  
shared_accesst::shared_accesst(locst& _locs) :
  locs(_locs)
{
}
  

void shared_accesst::rw_sets(
				statet& state,
				std::vector<bool>& is_shared,
				std::vector<sharedt::sett>& reads, 
				std::vector<sharedt::sett>& writes)
{
  
  unsigned nr_threads=state.threads.size();
  
  reads.clear();
  reads.resize(nr_threads);

  writes.clear();
  writes.resize(nr_threads);

  is_shared.clear();
  is_shared.resize(nr_threads, false);

  if(state.atomic_section_count)
  {
    return;
  }

  sharedt shared(state);

  unsigned current_thread=state.get_current_thread();

  for(unsigned 
      thr=0;
      thr<nr_threads;
      ++thr)
  {		
    if(state.threads[thr].active)
    {
      state.set_current_thread(thr);
      shared(reads[thr], writes[thr]);
      is_shared[thr]=!(reads[thr].empty() && writes[thr].empty());
    }                     
  }
  
  state.set_current_thread(current_thread);
}


symbol_exprt shared_accesst::thread_symbol(unsigned t)
{
  std::string thread_id="thread#"+i2string(t);
  return symbol_exprt(thread_id);
}

static bool overlap(const sharedt::sett& a, const sharedt::sett& b)
{
  for(sharedt::sett::const_iterator
	  it=a.begin();
	  it!=a.end();
	  ++it)
  {
    if(b.find(*it)!=b.end())
	  return true;
  }

  return false;
}

bool independent(
    const sharedt::sett& reads1,
    const sharedt::sett& writes1,
    const sharedt::sett& reads2,
    const sharedt::sett& writes2)
{
    return    !overlap(reads2, writes1)
           && !overlap(reads1, writes2)
  	   && !overlap(writes1, writes2);
}



/*******************************************************************\

Function: shared_accesst::target

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const goto_programt::instructiont& shared_accesst::current_instruction(statet& state, unsigned t)
{
  const statet::threadt &thread=state.threads[t];
  const loct &loc=locs[thread.pc];
  return *loc.target;
}
  

partial_order_reductiont::partial_order_reductiont(locst& _locs,
                                                   statet& _state) 
  : locs(_locs),
    state(_state),
  	parent(_state.node_ref),
    nr_threads(state.threads.size()),
    shared_access(locs)
{
  shared_access.rw_sets(state, is_shared, reads, writes);
}


/*******************************************************************\

Function: partial_order_reductiont::local_transition

  Inputs: state

 Outputs: number of thread to execute

 Purpose:

\*******************************************************************/


bool partial_order_reductiont::is_local(unsigned t)
{
  if(!state.threads[t].active) return false;
   
  if(state.atomic_section_count > 0)
    return true;
 
  const goto_programt::instructiont& 
   instruction=shared_access.current_instruction(state, t);   

  bool result= 
         enabled(state,t)
      && !is_shared[t] 
      && !instruction.is_backwards_goto();

  #ifdef DEBUG
  std::cout
    << "T"<<t<< " " << state.node_ref->number
    << " enabled " << enabled(state,t) 
    << " " << as_string(state.var_map.ns, instruction) 
    << " result " << result << std::endl;
  #endif

  return result;
}

unsigned partial_order_reductiont::local_transition()
{
  unsigned result=unsigned(-1);
  unsigned current=state.get_current_thread();

  for(;current + 1< state.threads.size()
       && !state.threads[current].active;  
       ++current);

  state.set_current_thread(current);

  for(unsigned t=0; t<state.threads.size(); ++t)
  {
    const goto_programt::instructiont& 
    instruction=shared_access.current_instruction(state, t);   

    if(instruction.is_start_thread())
    {
      thread_creators.insert(t);
    }
  } 
 
  if(is_local(current))
    return current;

  return result;
}


bool partial_order_reductiont::enabled(statet& state, unsigned t)
{
  return state.threads[t].active;
}


mono_partial_order_reductiont::mono_partial_order_reductiont(locst& _locs,
                                                             statet& _state) 
  :  partial_order_reductiont(_locs, _state),
     dcs(nr_threads)
{

}



void partial_order_reductiont::operator()(std::vector<unsigned>& interleaving)
{
  interleaving.reserve(nr_threads);
  interleaving.clear();
   
  unsigned local_t=local_transition(); 
 
  if(local_t!=unsigned(-1))
  {      
    interleave(interleaving, local_t);
  }
  else    
  {  
    int current_thread=state.get_current_thread();

    interleave(interleaving, current_thread);

    for(int t=nr_threads-1; t>=0; --t)
    {   
    	if(t!=current_thread)
	      interleave(interleaving, t);
    }
    
  }  
}

void mono_partial_order_reductiont::operator()(
  std::vector<unsigned>& interleaving)
{
  interleaving.reserve(nr_threads);
  interleaving.clear();
   
  unsigned local_t=local_transition(); 
 
  if(local_t!=unsigned(-1))
  {       
    interleave(interleaving, local_t);
  }
  else    
  {  
    int current_thread=state.get_current_thread();
  
    for(int t=nr_threads-1; t>=0; --t)
    {   
    	if(t!=current_thread)
	      interleave(interleaving, t);
    }
    
    interleave(interleaving, current_thread);
  }
}

void partial_order_reductiont::interleave(std::vector<unsigned>& interleaving, unsigned t)
{
  if(!enabled(state, t)) 
  {
    return;
  }

  interleaving.push_back(t); 
}


void mono_partial_order_reductiont::interleave(
  std::vector<unsigned>& interleaving,
  unsigned t)
{
  if(!enabled(state, t)) 
  {
    return; 
  }

  compute_dc(t);
        
  if(dependency_chaint::select(t, state.node_ref->dc, dcs[t]))
  {                       
    interleaving.push_back(t);  
  } 
}


void mono_partial_order_reductiont::compute_dc(unsigned i)
{	
  dependency_chaint::dependenciest dep(nr_threads, false);
  dependency_chaint &dc=dcs[i];

  if(thread_creators.count(i))
  {
    // created thread is woken up by its creator
    dep.push_back(false);
    dep[i]=true;
    dep[nr_threads]=false;
    dc.update(state.node_ref->dc, dep, i); // wakeup
  } 
  else 
  {
    for(unsigned j=0; j<nr_threads; ++j)
    {
      bool depend=!independent(reads[i], 
                               writes[i], 
                               state.threads[j].reads, 
                               state.threads[j].writes);
      dep[j]=i==j || depend;
    }

    dc.update(state.node_ref->dc, dep, i);  

    dc.set_writes(i, writes[i]);
    dc.set_reads(i, reads[i]);
  }
}



    
void mono_partial_order_reductiont::update(queuet& successors)
{
  
  for(queuet::iterator 
      it=successors.begin(); 
  	  it!=successors.end(); 
      ++it)
  {
    statet &successor=*it;    

    unsigned thread_nr=successor.get_current_thread();

    successor.node_ref->dc=dcs[thread_nr];

    if(is_shared[thread_nr])
    {
      successor.threads[thread_nr].reads= reads[thread_nr];
      successor.threads[thread_nr].writes=writes[thread_nr];
    }

  } 
}



    
    
void mono_partial_order_reductiont::print(const sharedt::sett& es)
{

  std::cout << "{";
  for(sharedt::sett::const_iterator 
      it=es.begin();
      it!=es.end();
      ++it)
  {
    std::cout << (it!=es.begin() ? "," : "") << *it;
  }

  std::cout << "}";
}    


node_reft last_expanded(node_reft node_ref, unsigned thread)
{
  while(!node_ref.is_nil() && !node_ref->expanded(thread))
  {
    if(node_ref->thread_nr==thread)
      return node_reft();		
    --node_ref;
  }
	
  return node_ref;
}
