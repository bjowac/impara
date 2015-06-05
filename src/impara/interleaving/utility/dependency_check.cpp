#include <cassert>
#include <string>
#include <algorithm>

#include "shared_step.h"

#include "dependency_check.h"

#define DEBUG

dependency_check_coarset::dependency_check_coarset
  (locst &_locs, 
   impara_var_mapt &_var_map, 
   const step_cont &steps,
   bool _only_pointers)
  : dependency_check_baset
    (_locs, 
     _var_map, 
     steps,
     _only_pointers)
{
  for(unsigned i=0; i<steps.size(); ++i)
    add(steps[i], i);
}


void dependency_check_coarset::operator()(const mem_sett &reads, 
                                          const mem_sett &writes, 
                                          step_sett& dep)
{
  // for each read, add the corresponding writes    
  insert_accessor(WRITE, reads, dep);
 
  // for each write, add the corresponding writes    
  insert_accessor(WRITE, writes, dep);

  // ditto for reads    
  insert_accessor(READ, writes, dep);
}
  
void dependency_check_coarset::operator()(unsigned i, step_sett& dep)
{
  // tracking dependencies inside atomic sections at ATOMIC_END
  if(steps[i]->inside_atomic())
    return;

  // retrieve the reads and writes of the current step i
  
  // for the read state, find steps writing the same state    
  step_memt::const_iterator reads_it=step_reads.find(i);
  
  if(reads_it!=step_reads.end())
  {
    const mem_sett &reads=reads_it->second;

    // for each read, add the corresponding writes    
    insert_accessor(i, WRITE, reads, dep);
  }
  
  // for the written state, find steps reading or writing the same state
  step_memt::const_iterator writes_it=step_writes.find(i);
  
  if(writes_it!=step_writes.end())
  {
    const mem_sett &writes=writes_it->second;

    // for each write, add the corresponding writes    
    insert_accessor(i, WRITE, writes, dep);

    // ditto for reads    
    insert_accessor(i, READ, writes, dep);
  }

  // dependency via thread creation
  thread_idt thread_nr=steps[i]->thread_nr;
  thread_creatort::const_iterator creator_it=thread_creator.find(thread_nr);
  if(creator_it!=thread_creator.end())
  {
    dep.insert(creator_it->second);
  }
}

void dependency_check_coarset::insert_accessor(rwkindt rwkind, const mem_sett & mem_set, step_sett &dest)
{
  for(mem_sett::const_iterator
      mem_it=mem_set.begin();
      mem_it!=mem_set.end();
      ++mem_it)
  {
    const memt &mem=*mem_it;
    const step_sett &step_set(rwkind == READ 
                            ? mem_step[mem].reads 
                            : mem_step[mem].writes);
    dest.insert(step_set.begin(), step_set.end());
  }
}


void dependency_check_coarset::insert_accessor(unsigned i, rwkindt rwkind, const mem_sett & mem_set, step_sett &dest)
{
    for(mem_sett::const_iterator
        mem_it=mem_set.begin();
        mem_it!=mem_set.end();
        ++mem_it)
    {
      const memt &mem=*mem_it;
      insert(i, rwkind == READ ? mem_step[mem].reads : mem_step[mem].writes, dest);
    }
}

void dependency_check_coarset::insert(unsigned i, const step_sett &from, step_sett &dest)
{
  for(step_sett::const_iterator
      it=from.begin();
      it!=from.end();
      ++it)
  {
    const stept &s=*it;
  
    if(s >= i)
      break;
      
    if(steps[s]->thread_nr == steps[i]->thread_nr)
      continue;
    
    dest.insert(s);
  }
}


void dependency_check_coarset::add(const impara_step_reft &step_ref, stept s)
{
  // not tracking dependencies inside atomic sections
  if(step_ref->inside_atomic())
    return;

  shared_stept::sett reads, writes;

  // get the shared accesses
  
  // NOTE: Here a more fine-grained analysis field-sensitive 
  //       analysis will be used
  shared_stept shared_step(locs, var_map, *step_ref, only_pointers);

  shared_step(reads, writes);

  for (shared_stept::sett::const_iterator 
       step_iterator = reads.begin();
       step_iterator != reads.end(); 
       ++step_iterator)
  {
    const exprt &read = *step_iterator;
    mem_step[read].reads.insert(s);
    step_reads[s].insert(read);
  }

  for (shared_stept::sett::const_iterator 
       step_iterator = writes.begin();
       step_iterator != writes.end(); 
       ++step_iterator)
  {
    const exprt &write = *step_iterator;
    mem_step[write].writes.insert(s);
    step_writes[s].insert(write);
  }
  
  // thread creation
  if(s>0)
  {
    thread_idt max_thread=steps[s]->max_thread;
  
    if(max_thread > steps[s-1]->max_thread)
      thread_creator[max_thread]=s-1;
  }
  
}
