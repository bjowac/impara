#include <cassert>
#include <string>
#include <algorithm>

#include <util/find_symbols.h>

#include "../utility/shared_step.h"

#include "../utility/dependency_check.h"

#include "symex/from_ssa.h"

#include "symex/propagation.h"

#include "happens_before.h"

#include "node.h"

//#define DEBUG


class happens_beforet
{
public:
  typedef std::vector<impara_step_reft> step_cont;

  happens_beforet(locst &__locs,
                  impara_var_mapt &__var_map,
                  step_cont& __steps,
                  node_reft __terminal,  
                  backtrackt &__backtrack,
                  bool __only_pointers);
 
  struct racet
  {
    node_reft start;
    node_reft middle;
    node_reft end;
    impara_step_reft first;
    impara_step_reft second;
    impara_step_reft minimal_step;
    impara_step_reft bt_step;
    unsigned thread_nr;
  };
  
  backtrackt &backtrack;    
  
  void output(std::ostream &out);  

private:
  step_cont& steps;  
  node_reft terminal;
  
  typedef std::vector<clockst> clocks_cont;
  clocks_cont step_clocks;   // step   x thread -> step
  clocks_cont thread_clocks; // thread x thread -> step

  unsigned get_nr_of_threads(step_cont &s);

  void add(impara_step_reft begin, impara_step_reft end);

  void do_step(unsigned j);

  void compute_summary( 
                      unsigned j,
                      class path_summaryt &summary);

  void do_summary( 
                  node_reft node,
                  bool read_flag);

  // accessing the same memory locatoin
  void potential_races();
  // infeasible or redundant races
  void refine_races();

  bool co_enabled(unsigned i, unsigned j);
  unsigned minimal(unsigned i, unsigned j);
  unsigned skip_atomic(unsigned i);

  void add_race(unsigned i, unsigned j);
  bool get_race(unsigned i, unsigned j, racet &race);

  node_reft next_node(unsigned i);

  locst &locs;
  impara_var_mapt &var_map;
  dependency_check_coarset dep;
  unsigned nr_of_threads;

  void writes(const exprt &src, 
            unsigned from,
            unsigned until,
            std::vector<unsigned> &result) const;
  
  
  void report_race(const racet &race) const;
  void output(std::ostream &out, unsigned i);  
};


void happens_before(locst &locs,
                  impara_var_mapt &var_map,
                  happens_beforet::step_cont& steps, 
                  node_reft terminal,
                  backtrackt &backtrack,
                  bool only_pointers)
{
  happens_beforet hb(locs, var_map, steps, terminal, backtrack, only_pointers);
}




happens_beforet::happens_beforet(
    locst &__locs,
    impara_var_mapt &__var_map,
    step_cont& __steps,
    node_reft __terminal,
    backtrackt &__backtrack,
    bool __only_pointers)
  : backtrack(__backtrack),
    steps(__steps),
    terminal(__terminal),
    locs(__locs),
    var_map(__var_map),
    dep(locs, var_map, steps, __only_pointers),
    nr_of_threads(get_nr_of_threads(steps))
{
  // intialise clocks
  clockst clocks(nr_of_threads);
  step_clocks.resize(steps.size(), clocks);
  thread_clocks.resize(nr_of_threads, clocks);     
    
  potential_races();
  
  #ifdef DEBUG
  
  unsigned added=backtrack.size() - size;
  
  if(added)
  {
    std::cout << "happens_beforet " << backtrack.size() - size << " backtracking points" << std::endl;
  }
  #endif
}

/*
  Function: get_nr_of_threads(step_cont &steps)
  Input: a sequence of steps
  Output: total number of threads observed in the execution
  Summary:
 */
unsigned happens_beforet::get_nr_of_threads(step_cont &steps)
{
  unsigned result=0;

  for(unsigned i=0; i<steps.size(); ++i)
  {
    unsigned thread_nr=steps[i]->thread_nr;
    result=std::max(thread_nr, result);  
  }

  ++result;
  
  return result;
}

/*
  Function: co_enabled(unsigned i, unsigned j)
  Input: two step indices
  Output: whether the steps are co-enabled or not:boolean
  Summary: 
          return true if proc(j) is created before than the
	  max-thread maintained by thread i. 
 */

bool happens_beforet::co_enabled(unsigned i, unsigned j)
{
  //[svs]: THis check can be unsound -- better to treat 
  //       every pair of actions as co-enabled.
  return steps[j]->thread_nr<=steps[i]->max_thread;
}



void happens_beforet::do_summary(
                                 node_reft node,
                                 bool read_flag)
{
  typedef path_summaryt::thread_sett thread_sett;

  path_summaryt &summary=node->path_summary;
  path_summaryt::accesst &access=read_flag ? summary.reads : summary.writes;

  for(path_summaryt::accesst::const_iterator
      access_it=access.begin();
      access_it!=access.end();
      ++access_it)
  {
    exprt mem=access_it->first;
    const thread_sett &thread_set=access_it->second;

    std::set<exprt> reads, writes;

    if(read_flag)
      reads.insert(mem);
    else
      writes.insert(mem);

    for(thread_sett::const_iterator 
        thread_it=thread_set.begin();
        thread_it!=thread_set.end();
        ++thread_it)
    {
      unsigned thread_j=*thread_it;
    
      std::set<unsigned> dep_steps;

      dep(reads, writes, dep_steps);
    
      unsigned i_option=unsigned(-1);

      for(std::set<unsigned>::const_iterator
         it=dep_steps.begin();
         it!=dep_steps.end();
         ++it)
      {
        unsigned i=*it;  
        
        unsigned thread_i=steps[i]->thread_nr;
    
        // no other depencency
        if(thread_j >= thread_clocks.size() || thread_clocks[thread_j][thread_i] < i)
        {
          i_option=i;
        } 
      }

      if(i_option!=unsigned(-1))
      {
        unsigned i=i_option;
        impara_step_reft bt_step=steps[skip_atomic(i)];
        node_reft bt_node_ref=bt_step->node_ref;
        node_equiv_classt &equiv_class=bt_node_ref.get_node_equiv_class();
        if(thread_j >= equiv_class.global_vector->size())
        {
          std::cout << "Thread j=" << thread_j 
                    << " hasn't been started yet: ";
                    
          for(nodet::thread_sett::iterator 
	      it=bt_node_ref->expanded_threads.begin();
	      it!=bt_node_ref->expanded_threads.end();
	      ++it)
	  {
	    std::cout << *it;
	  }
							           
	  std::cout << std::endl;
                    
          return;
        }

        // TODO: if not enabled try its thread creator instead


        if( bt_node_ref->expanded_threads.count(thread_j) != 0)
        {
          #ifdef DEBUG
          std::cout << "  ==> Not Added: thread already expanded" << std::endl;
          #endif
          return;
        }
            
        if(bt_node_ref->sleep.count(thread_j) != 0)
        {
          #ifdef DEBUG      
          std::cout << "  ==> Not Added: thread sleeping" << std::endl;
          #endif
          return;
        }



        backtrack[bt_node_ref].insert(thread_j);
      }
    }
  }
}

void happens_beforet::do_step(unsigned j)
{
  impara_step_reft step_ref(steps[j]);

  if(step_ref->inside_atomic())
  {
    return;
  }

  unsigned thread_j=step_ref->thread_nr;

  clockst &thread_clocks_j=thread_clocks[thread_j];

  
  std::set<unsigned> dep_steps;

  dep(j, dep_steps);

  unsigned i_option=unsigned(-1);

  for(std::set<unsigned>::iterator
      it=dep_steps.begin();
      it!=dep_steps.end();
      ++it)
  {
    unsigned i=*it;  
    
    unsigned thread_i=steps[i]->thread_nr;
    
    // no other depencency
    if(co_enabled(i,j) && thread_clocks_j[thread_i] < i)
    {

      i_option=i;
    } 
  }
  
  if(i_option!=unsigned(-1))
  {
    unsigned i=i_option;
 
    add_race(i,j);
  }

  clockst &cv=step_clocks[j];
  cv=thread_clocks[thread_j]; 
  
  for(std::set<unsigned>::const_iterator
	    it=dep_steps.begin();
      it!=dep_steps.end();
      ++it)
  {
    unsigned i=*it;
    
    cv.max(step_clocks[i]);
  }

  // update the clocks
  cv[thread_j]=j;
    
  thread_clocks[thread_j]=cv;

  #ifdef DEBUG
  //output(std::cout, dep, j);
  #endif
}



void happens_beforet::compute_summary( 
                                 unsigned j,
                                 path_summaryt &summary)
{
  // retrieve the shared accesses of the step
  typedef dependency_check_coarset::mem_sett mem_sett;

  mem_sett &reads=dep.step_writes[j], 
                  &writes=dep.step_reads[j];

  unsigned thread_nr=steps[j]->thread_nr;

  bool read_flag=true;

  for(mem_sett::const_iterator it=reads.begin();
     it!=reads.end(); ++it)
  {
    summary.update(*it, thread_nr, read_flag);    
  }

  read_flag=false;

  for(mem_sett::const_iterator it=writes.begin();
     it!=writes.end(); ++it)
  {
    summary.update(*it, thread_nr, read_flag);    
  }

  // TODO: thread creation 

}

void happens_beforet::potential_races()
{
  // compute backtracks
  for(unsigned i=0; i<steps.size(); ++i)
  {
    do_step(i);
  }

  node_reft::listt &covered_by=terminal->covered_by;

  for(unsigned i=0; i<covered_by.size(); ++i)
  {
    terminal->path_summary.join(covered_by[i]->path_summary);

    do_summary(covered_by[i], true);
    do_summary(covered_by[i], false);
  }

  path_summaryt summary;
  node_reft prev_node;

  for(int i=steps.size()-1; i>=0; --i)
  {
    // update the summary at current node
   node_reft curr_node=steps[i]->node_ref;

   if(curr_node->has_label() && prev_node!=curr_node)
   {
     curr_node->path_summary.join(summary);  
   }

    compute_summary(i, summary);
    prev_node=curr_node;
  }
}

unsigned happens_beforet::skip_atomic(unsigned i)
{
  unsigned k=i;

  while(k>0 && steps[k]->is_atomic())
    --k;
    
  return k;  
}


/*******************************************************************\
 
Function: happens_beforet::next_node

  Inputs: step number

 Outputs: node after the step in the path

 Purpose: 

\*******************************************************************/
        
node_reft happens_beforet::next_node(unsigned i)
{
  node_reft node_ref=steps[i]->node_ref;

  for(unsigned j=i+1; j<steps.size(); ++j)
  {
    node_reft other_node_ref=steps[j]->node_ref;
    if(node_ref!=other_node_ref)
      return other_node_ref;
  }

  return terminal;
}

void happens_beforet::writes(const exprt &src, 
            unsigned from,
            unsigned until,
            std::vector<unsigned> &result) const
{
  if(src.is_true() || src.is_false())
    return;

  std::set<exprt> symbols;
  
  find_symbols(from_ssa(src), symbols);

  // replace the symbols in src by the suitable SSA assignments
  for(unsigned i=from; until<i && i>0;--i)
  {
    const impara_stept& step=*steps[i];
    
    if(step.full_lhs.is_not_nil())
    {
      exprt lhs=from_ssa(step.full_lhs);

      if(symbols.count(lhs))
        result.push_back(i);
    }
  }
}


bool happens_beforet::get_race(unsigned i, unsigned j,
                               racet &race)
{
  unsigned k=minimal(i,j);
  
  if(k==unsigned(-1))
  {
    #ifdef DEBUG
    std::cout << "Steps " << steps[i]->node_ref->number << " "
              << steps[j]->node_ref->number 
              << " no minimal step found" << std::endl;
    #endif
  
    return false;
  }


  #ifdef DEBUG
  std::cout << "Minimal step " << steps[k]->node_ref->number << " "
            << " i = " << steps[i]->node_ref->number << std::endl
            << " j = " << steps[j]->node_ref->number << std::endl;
  #endif


  i=skip_atomic(i);

  bool done=false;

  for(unsigned l=k; l<j && !done; ++l)
  {
    if(steps[l]->is_assume())
    {
      std::vector<unsigned> write_steps;
      exprt guard=from_ssa(steps[l]->guard);

      #ifdef DEBUG
      std::cout << "Step N" << steps[l]->node_ref->number << " S" << l << " " << steps[l]->thread_nr << " assumption " << from_expr(var_map.ns, "", guard ) << std::endl;
      std::cout << "  ~~~~ N" << steps[i]->node_ref->number << " " << i << " " << steps[i]->thread_nr << " " << from_expr(var_map.ns, "", steps[i]->guard) << " => "
                                         << steps[i]->ssa_lhs << " := " << steps[i]->ssa_rhs << std::endl;
      #endif
      
      writes(steps[l]->guard, i, 0, write_steps);

      for(unsigned m=0; m<write_steps.size(); ++m)
      {
        unsigned s=write_steps[m];
        const impara_stept &write_step=*steps[s];
        exprt what=from_ssa(write_step.ssa_lhs);
        exprt guard_repl=guard;
        replace_expr(what, write_step.ssa_rhs, guard_repl); 
        simplify(guard_repl, var_map.ns);
      
        #ifdef DEBUG
        std::cout << "  " << s
                  << " T " << write_step.thread_nr << " step " << from_expr(var_map.ns, "", what) << " := " << from_expr(var_map.ns, " ", write_step.ssa_rhs) 
                  << "\n  ==>" << from_expr(var_map.ns, "  ", guard_repl) << std::endl;
        #endif
      
        if(guard_repl.is_false())
        {
          
          i=skip_atomic(s);
          done=true;
          break;          
        }
        else
        {
          done=true;
          break;
        }
      }
    }
  }


  race.first=steps[i];
  race.second=steps[j];
  race.minimal_step=steps[k];
  race.thread_nr=steps[k]->thread_nr;

  race.bt_step=steps[i];
  race.start=race.bt_step->node_ref;
  race.middle=steps[k]->node_ref;
  race.end=next_node(j);

  #ifdef DEBUG
  report_race(race);
  #endif

  return true;
}


void happens_beforet::add_race(unsigned i, unsigned j)
{
  racet race;

  #ifdef DEBUG
  std::cout << "add_race " << std::endl;
  #endif

  if(!get_race(i,j,race))
    return;

  #ifdef DEBUG
  report_race(race);
  #endif

  node_reft bt_node_ref=race.bt_step->node_ref;

  node_equiv_classt &equiv_class=bt_node_ref.get_node_equiv_class();

  if(race.thread_nr >= equiv_class.global_vector->size())
  {
    return;
  }


  if( bt_node_ref->expanded_threads.count(race.thread_nr) != 0)
  {
    #ifdef DEBUG
    std::cout << "  ==> Not Added: thread already expanded" << std::endl;
    #endif
    return;
  }
      
  if(bt_node_ref->sleep.count(race.thread_nr) != 0)
  {
    #ifdef DEBUG      
    std::cout << "  ==> Not Added: thread sleeping" << std::endl;
    #endif
    return;
  }

  backtrack[bt_node_ref].insert(race.thread_nr);
}
  

void happens_beforet::report_race(const happens_beforet::racet &race) const
{
    propagationt prop(var_map.ns);

    std::cout << "Potential race " << std::endl;
    std::cout << "  " << race.first->pretty(var_map.ns, locs, prop) 
              << std::endl;
    std::cout << "  with " << std::endl;
    std::cout << "  " << race.second->pretty(var_map.ns, locs, prop) 
              << std::endl;
    std::cout << "  backtracking thread " << race.thread_nr
              << " from minimal step " << std::endl;
    std::cout << "  to " << race.bt_step->pretty(var_map.ns, locs, prop) 
              << std::endl;
}
   	      
unsigned happens_beforet::minimal(unsigned i, unsigned j)
{
  impara_step_reft bt_step=steps[skip_atomic(i)];
  node_reft bt_node=bt_step->node_ref;

  std::vector<unsigned> candidates;

  for(unsigned k=i+1; k<j; ++k)
  {       
    if(steps[k]->inside_atomic())
      continue;

    bool dep=false;
 
 
 		unsigned thread_nr=steps[k]->thread_nr;
 
 		dep=(i<=step_clocks[k-1][thread_nr]);
 
 		/*
    for(unsigned t=0; !dep && t<step_clocks[k].size(); ++t)
    {
      dep=(i<=step_clocks[k][t]); 

//      #ifdef DEBUG
      std::cout << "   thread " <<t << " node " 
                << steps[k]->node_ref->number
                << "(" << k << ")"
                << " dep with " 
                << steps[step_clocks[k][t]]->node_ref->number 
                << "(" << step_clocks[k][t] << ")"
                << std::endl;
//      #endif
    }
    */
    
    if(dep) continue;

    candidates.push_back(k);
  }
  
  candidates.push_back(j);
  
  for(unsigned i=0; i<candidates.size(); ++i)
  {
    unsigned candidate=candidates[i];
    unsigned thread_nr=steps[candidate]->thread_nr;
      
    if(bt_node->expanded_threads.count(thread_nr))
    {
      #ifdef DEBUG
      std::cout << "Node " << steps[candidate]->node_ref->number << std::endl;
 
      std::cout << "Already expanded here " << thread_nr << std::endl;
      #endif
      return -1;    
    }
  }
  
  backtrackt::iterator it=backtrack.find(bt_node);

  if(it!=backtrack.end())
  {
    thread_sett &thread_set=it->second;
 
    for(unsigned i=0; i<candidates.size(); ++i)
    {
      unsigned candidate=candidates[i];
      unsigned thread_nr=steps[candidate]->thread_nr;
        

      if(thread_set.count(thread_nr)) 
      {
        #ifdef DEBUG
        std::cout << "empty thread set " << std::endl;
        #endif
        return -1;
      }
    }
  }
  
  return candidates.front();  
}


void happens_beforet::output(std::ostream &out)
{
  for(unsigned i=0; i<steps.size(); ++i)
  {
    output(out, i);
  }  
}

void happens_beforet::output(std::ostream &out, 
   unsigned i)
{
  std::cout << "  C(" << i << ") = " << step_clocks[i].pretty() << std::endl ;  

  std::set<unsigned> dep_steps;

  std::cout << "  inside atomic " << steps[i]->inside_atomic() << std::endl;
  std::cout << "  dep(" << i << ") = ";

  dep(i, dep_steps);
  for(std::set<unsigned>::const_iterator
      it=dep_steps.begin();
      it!=dep_steps.end();
      ++it)
  {
    std::cout << *it << " ";
  }
  
  std::cout << std::endl;
  std::cout << std::endl;
  
}


