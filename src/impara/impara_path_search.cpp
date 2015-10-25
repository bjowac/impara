/*******************************************************************\

Module: Forward Path Search

Author: Daniel Kroening, kroening@kroening.com
        Bjoern Wachter, bjoern.wachter@gmail.com

\*******************************************************************/

#include <sstream>
#include <fstream>
#include <cstdlib>
#include <iostream>

#include <algorithm>


#include <util/prefix.h>
#include <util/i2string.h>
#include <util/time_stopping.h>
#include <util/expr_util.h>
#include <util/simplify_expr.h>
#include <util/std_types.h>
#include <util/arith_tools.h>

#include <solvers/flattening/bv_pointers.h>
#include <solvers/sat/satcheck.h>


#include <symex/symex.h>
#include "impara_path_search.h"

#include <interleaving/mpor/partial_order_reduction.h>

#include <symex/build_goto_trace.h>
#include <csignal>

//#define DEBUG


/*******************************************************************\

Function: impara_path_searcht::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

safety_checkert::resultt impara_path_searcht::operator () (
  const goto_functionst &goto_functions)
{
  reset_statistics();

  status() << "size of a node " << sizeof(nodet) << eom;



  status() << "Building location map" << eom;
  locs.build(goto_functions);

  all_properties=options.get_bool_option("all-properties");
  do_show_vcc = options.get_bool_option("show-vcc"); 
  do_wordlevel_interpolation=options.get_bool_option("wordlevel-interpolation");

  #ifdef DEBUG

  for(goto_functionst::function_mapt::const_iterator 
    it=goto_functions.function_map.begin();
    it!=goto_functions.function_map.end();
    it++)
  {
    const goto_functionst::goto_functiont &goto_function = it->second;

    status() << "==================" << it-> first << "==================" << eom;    
    status() << goto_function.type.pretty() << eom;

  }
  #endif

  try
  {
    compute_cutpoints();

    initialize_property_map(goto_functions);

    if(property_map.empty())
    {
      return safety_checkert::SAFE;
    }

    search();

    report_statistics();
    report_limits();      

    dot_output();  
 }
 
  catch(unsafe_exception)
  {
    report_statistics();
    dot_output(); 
    return safety_checkert::UNSAFE;
  }

  catch(const char *msg)
  {
    report_statistics();

    std::string error_msg("\nException:\n");
    error_msg += msg;
    error() << error_msg << eom;
    return safety_checkert::ERROR;
  }
  
  catch(const std::string &msg)
  {
    report_statistics();
    error() << ("\nException:\n" + msg) << eom;
    return safety_checkert::ERROR;
  }
  
  catch(std::bad_alloc& ba)
  {
    report_statistics();

    std::string what(ba.what());
    error() << ("\nException\nbad alloc "+what) << eom;  
    return safety_checkert::ERROR;
  }
  
  catch(...)
  {
    report_statistics();
    error() << "\nUnexpected exception\n" << eom;  
    return safety_checkert::ERROR;
  } 


  if(number_of_failed_properties>0)
  {
    return safety_checkert::UNSAFE;
  }
  else
  {
    return safety_checkert::SAFE;
  }
}

void impara_path_searcht::print_queue(queuet& queue) 
{
  status() << "  Q = { " ;
  for(queuet::iterator it = queue.begin(); it!=queue.end(); ++it) {
     const statet& state = *it;
     status() << (it!=queue.begin() ? ", " : "") 
              << "N" << state.node_ref->number << "@" 
              << state.threads[state.get_current_thread()].pc
              << (state.node_ref->is_covered() ? "C" : "U");
	}
  status() << "}"<< eom;
}


/*******************************************************************\
 
Function: impara_path_searcht::select_state

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

impara_path_searcht::queuet::iterator impara_path_searcht::select_state(queuet& queue) {

  impara_path_searcht::queuet::iterator result=queue.end();

  if(queue.size())
  {
    bool found=false;

    for(unsigned limit=0; !found; limit+=5)
    {
      result=queue.end();

      unsigned candidates=0;

      do {
	--result;
	bool covered=result->node_ref->is_covered();

	if(covered)
	  continue;

	++candidates;
	unsigned cost=result->get_no_thread_interleavings() +
	  result->get_no_unwindings();
	found=!covered;
	found=found && cost <= limit;
      } while(!found && result!= queue.begin());


      if(candidates==0)
        break;
    }


    if(found) 
    {
      queuet::iterator cov = result;
      ++cov;
      queue.splice(result,queue,cov,queue.end());
    } else
    {
      result=queue.end();
    }
  }

  return result;
}


/*******************************************************************\
 
Function: impara_path_searcht::abstract_transformer

  Inputs:

 Outputs:

 Purpose: compute the label of a newly created node

\*******************************************************************/

exprt impara_path_searcht::abstract_transformer(statet &state)
{

  exprt result=true_exprt();

  // determine state of explicit variables

  for(unsigned i=0; i<state.shared_vars.size(); ++i)
  {
    const statet::var_statet &var_state=state.shared_vars[i];	  
    const exprt &value=var_state.value;
    const symbol_exprt &ssa_symbol=var_state.ssa_symbol;

    const std::string &identifier=id2string(ssa_symbol.get(ID_C_full_identifier));

    if(!has_prefix(identifier, "trace_automaton::")
       && !explicit_variables.count(identifier)
       // && !has_prefix(identifier, "c::start_routine")
       && !has_prefix(identifier, "c::__CPROVER::"))
      continue;

    if(value.id()==ID_constant)
    {			
      symbol_exprt symbol(identifier, ssa_symbol.type());

      exprt tmp=equal_exprt(symbol, value);
      impara_conjoin(tmp, result, ns);
    }  
  }
  
  for(unsigned i=0; i<state.threads.size(); ++i)
  {
    const statet::threadt &thread=state.threads[i];		
    const statet::var_valt &local_vars=thread.local_vars;
    for(unsigned j=0; j<local_vars.size(); ++j)
    {
      const statet::var_statet &var_state=thread.local_vars[j];	  
      const exprt &value=var_state.value;
			const symbol_exprt &ssa_symbol=var_state.ssa_symbol;

      const std::string &identifier=id2string(ssa_symbol.get(ID_C_full_identifier));
      
      if(!has_prefix(identifier, "trace_automaton::")
         && !explicit_variables.count(identifier)
         // && !has_prefix(identifier, "c::start_routine")
         && !has_prefix(identifier, "c::__CPROVER::"))
        continue;

      if(value.id()==ID_constant)
      {			
	      symbol_exprt symbol(identifier, ssa_symbol.type());
        exprt tmp=equal_exprt(symbol, value);
		  	impara_conjoin(tmp, result, ns);
      }  	  	
    }
  }

  return result;
}



/*******************************************************************\
 
Function: impara_path_searcht::succ

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool impara_path_searcht::succ(unsigned t, 
                        statet& state, 
                        queuet& successors,
      			bool local)
{

  bool result=true;

  state.set_current_thread(t);
  
  if(drop_thread(state))
  {
    state.disable_current_thread();
    return false;
  }

  if(!state.threads[t].active)
    return false;

  /** decide if the corresponding node needs a label */
  const goto_programt::instructiont& instruction=*state.get_instruction();
  bool do_labeling = true;
  bool check_assume=false;
  bool feasible=true;
  int branch=-1;

  switch(instruction.type)
  {
    case GOTO:
      branch=decide_branch(state);
      do_labeling=state.threads.size()>1;
      break;
    case ASSERT:
      check_assertion(state);
      do_labeling=false;
      break;
    case START_THREAD:
      if(
        do_assertions &&
        refine(state, 
                initial_node_ref,
                true_exprt(), 
                false_exprt(), 
                symex_solver_stats))
      {         
        feasible=false;
	      result=false;
      } else
      {
        // statistics about number of threads
        if(number_of_threads <= state.threads.size())
          ++number_of_threads;
      }
      break;
    case ASSUME:  
      check_assume=true;     
      do_labeling=false;
      break;
    case ASSIGN:
    case FUNCTION_CALL:
      do_labeling=state.threads.size()>1;
      break;
    default:  
      do_labeling=false;
      break;
  }  

  if(state.threads.size()>1)
  {
    if(state.atomic_section_count)
      do_labeling=false;
  }

  if(!feasible)
    return false;

  //update_explicit_variables(state, t);
 
  queuet::iterator first_state=--successors.end(); // TODO: change this
  
  absolute_timet symex_start_time=current_time();
 
  switch(branch)
  {
    case 0:
      impara_symex_goto(state, false);
      break;
    case 1:
      impara_symex_goto(state, true);
      break;
    default:
      impara_symex(state, successors);
      break;
  }

  symex_time += current_time() - symex_start_time;

  if(check_assume && do_assertions)
  {

    if(instruction.guard.is_false())
    {
    }
    else {
    
      exprt guard=
        state.read_no_propagate(instruction.guard);
      
      if(refine(state, 
             initial_node_ref,
             true_exprt(), 
             not_exprt(guard), 
             symex_solver_stats))
      {                    
        state.disable_current_thread();
        state.history->guard=not_exprt(guard);
        
        if(state.atomic_section_count)
        {
          --state.atomic_section_count;
          state.history->set_atomic_end(true);
        }
      } 
      else
      {
        state.history->guard=guard;
      } 
    } 
  }
  
  for(queuet::iterator
      it=first_state;
      it!=successors.end();
      ++it)
  {
    statet& successor=*it;
    
    node_reft &node_ref=successor.node_ref;
    
    node_ref=nodes.new_node(successor);

    do_labeling=do_labeling || cutpoints.count(successor.pc());

               
    if(do_labeling)
    {    
      exprt label=abstract_transformer(successor);
      node_ref->refine(ns, merge, label);
    }
  }

  return result;
}


/*******************************************************************\
 
Function: impara_path_searcht::check_assertion

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void impara_path_searcht::check_assertion(statet &state)
{
  ++assertion_checks;

	if(!do_assertions)
    return;

  const goto_programt::instructiont& 
    instruction=*state.get_instruction();

  irep_idt property_name=instruction.source_location.get_property_id();

  property_entryt &property_entry=property_map[property_name];
  
  if(property_entry.status==FAIL)
    return; // already failed
  else if(property_entry.status==NOT_REACHED)
    property_entry.status=PASS; // well, for now!

  exprt 
    assertion=state.read_no_propagate(instruction.guard);

  if(do_show_vcc)
  {
    status() << "Checking assertion " << from_expr(var_map.ns, "", assertion) << eom;  
  }

  if(assertion.is_true()) return; // no error, trivially

  if(!refine(
     state, 
  	 initial_node_ref, 
  	 true_exprt(), 
  	 assertion, 
  	 assert_solver_stats,
  	 true)) 
  {
		error_node=state.node_ref;

    property_entry.error_trace=error_trace;
    property_entry.status=FAIL;
    number_of_failed_properties++;


    // exit after the first failed assertion
    if(!all_properties)
      throw unsafe_exception();      
  }       
}



bool impara_path_searcht::drop_state(statet &state)
{

  if(state.node_ref->number > node_limit)
    return true;

  // depth
  if(int(depth_limit)!=std::numeric_limits<int>::max()
    && state.get_depth()>depth_limit) 
    return true;

  return false;
}

bool impara_path_searcht::drop_thread(statet &state)
{
  // thread limit -- no more threads, please!
  if(state.threads.size() >= thread_limit 
    && state.get_instruction()->is_start_thread())
    return true;

  // context bound -- no more context switches, please!
  if(int(context_bound)!=std::numeric_limits<int>::max()
    && state.get_no_thread_interleavings()>context_bound) 
    return true;

  unsigned unwindings=state.get_no_unwindings();

  if(unwindings>10)
    status() << "Loop " << state.get_instruction()->source_location
      << " : unwindings " << unwindings << eom;


  if(unwindings>unwind_limit)
    return true;

  return false;
}



void impara_path_searcht::update_explicit_variables(statet &state, unsigned t)
{
  if(!state.threads[t].active)
    return;

  const goto_programt::instructiont&
    instruction=*state.get_instruction();
  
  if(instruction.is_assume())
  {
    const exprt guard=instruction.guard;
  	
    if(guard.id()==ID_and)
    {
      // TODO
    }
    else
    {  			
      if(guard.id()==ID_equal)
      {
        const exprt &op0=guard.op0();
	const exprt &op1=guard.op1();
				
        if(op0.id()==ID_symbol && op1.id()==ID_constant)
        {
	  const symbol_exprt &symbol_expr=to_symbol_expr(op0);
	  const std::string identifier=id2string(symbol_expr.get_identifier());

	  if(!explicit_variables.count(identifier))
	    std::cout << "explicit variable " << identifier << std::endl;

	  explicit_variables.insert(identifier);
        }
      }
    }
  }
}


/*******************************************************************\
 
Function: impara_path_searcht::decide_branch

  Inputs:

 Outputs: return value true iff branch was resolved

 Purpose:

\*******************************************************************/

int impara_path_searcht::decide_branch(statet& state)
{
  int result=-1;

  loc_reft target;

  const goto_programt::instructiont& 
    instruction=*state.get_instruction();

  if(!do_eager)
   return result;
  	
  if(instruction.guard.is_true())
  	return result;

  if(instruction.is_goto())
  {
    exprt guard=state.read_no_propagate(instruction.guard);
    exprt guard_prop=state.read(guard);
  
    if(guard.id()==ID_symbol)
    {
      if(has_prefix(id2string(to_symbol_expr(guard).get_identifier()), 
                    "symex::nondet"))
        return -1;
    }
  
    if(guard.is_false())
      result=0;
    else if(guard.is_true())
      result=1;
    else if(guard.is_nil())
      result=-1;
    
    
    if(
      refine(state, 
           initial_node_ref,
           true_exprt(), 
           not_exprt(guard), 
           symex_solver_stats))
    {     
      result=0;
    }
    else if(
      refine(state, 
           initial_node_ref,
           true_exprt(), 
           guard, 
           symex_solver_stats))
    {     
      result=1;
    }
  
  }   

  return result; 
}


/*******************************************************************\

Function: impara_path_searcht::expand

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void impara_path_searcht::expand(statet& state, queuet::iterator& choice)
{
  
  #ifdef DEBUG
  status() << "Expanding" << eom;
  #endif
  
  if(state.node_ref->get_label().is_false())
    return;

  successors.clear();
  threads.clear();

  mono_partial_order_reductiont por(locs, state);

  por(threads);

  if(covered(state))
  {    
    return;
  }

  if(threads.size()==1)
  {    
    state.set_current_thread(threads.back());
    
    successors.splice(successors.end(),queue,choice);
    succ(threads.back(), state, successors, true);
  }
  else
  {
    // potentially multiple interleavings
    for(unsigned i=0; i<threads.size(); ++i)
    {    
      successors.push_back(state);
      statet &s=successors.back();        
      succ(threads[i], s, successors, false);
    }

    queue.erase(choice);
  }

  por.update(successors);

  queue.splice( do_bfs ? queue.begin() : queue.end(), successors);
}

/*******************************************************************\

Function: impara_path_searcht::search

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void impara_path_searcht::search()
{
  status() << "Starting search" << eom;

  queue.push_back(initial_state());
    
  #ifdef DEBUG
  queue.back().output(status());
  #endif

  initial_node_ref = queue.front().node_ref;

  while(true)
  {  
    queuet::iterator choice=select_state(queue);

    if(choice==queue.end())
    {       
      return;
    } 

    statet &state=*choice;

    if(drop_state(state))
    {
      // make sure that this node cannot cover anything
      state.node_ref->refine(ns, merge, false_exprt());
      queue.erase(choice);
      ++number_of_dropped_states;
      continue;
    }
  
    // compute successors and pursue
    if(!has_enabled(state))
    {
      queue.erase(choice);
      ++number_of_finished_states;
      continue;
    }

    expand(state, choice);
  }
}

/*******************************************************************\

Function: impara_path_searcht::report_limits

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void impara_path_searcht::report_limits()
{
  unsigned undef=std::numeric_limits<int>::max();
  
  if(thread_limit != undef)
  {
    status() << "maximal number of threads " << thread_limit << eom;
  }
  
  if(node_limit != undef)
  {
    status() << "maximal number of nodes   " << node_limit << eom;
  }

  if(unwind_limit != undef)
  {
    status() << "maximal number of unwindings " << unwind_limit << eom;
  } 
    
  if(depth_limit != undef)
  {
    status() << "maximal path length " << depth_limit << eom;
  } 
    
  if(context_bound != undef)   
  {
    status() << "context bound " << context_bound << eom;
  }  
  
}

void impara_path_searcht::report_statistics()
{
  std::ostream &str=statistics();
  str << "Locs:    " << locs.loc_vector.size() << "\n"
      << "Threads: " << number_of_threads << std::endl;
  str << "Nodes:   " << nodes.node_counter << "\n"
      << "States:  " << (queue.size() + number_of_dropped_states + number_of_finished_states) << std::endl;
  str << "Cover checks: " << std::endl
      << " * ordinary " << cover_checks_ok << " / " << cover_checks_total << std::endl;

  if(do_force_cover)
  {
    str << " * force    " << force_cover_checks_ok << " / " << force_cover_checks_total << std::endl;  
  }
  
  str << "Number of uncoverings " << number_of_uncoverings << std::endl;
 
  str << "Refinements: " << std::endl
      << " * nr  " << refinements << std::endl;

  str << "Cover checks" << std::endl;
  cover_solver_stats.output(str);
  str << std::endl;

  str << "Force-cover checks" << std::endl;
  force_cover_solver_stats.output(str);
  str << std::endl;

  str << "Assertion checks " << assertion_checks << std::endl;
  assert_solver_stats.output(str);
  str << std::endl;
  
  str << "Symex checks" << std::endl;
  symex_solver_stats.output(str);
  str << std::endl;
  
    

  statistics() << eom;

  time_periodt total_time=current_time()-start_time;
  statistics() << "Runtime: " << total_time << "s total " << messaget::eom
               << "  Symex " << symex_time << " s " << messaget::eom 
               << "  Close " << close_time  << " s " << messaget::eom 
               << "  Force " << force_time  << " s " << messaget::eom
               << "  Domain "<< domain_time << " s" << messaget::eom
               << messaget::eom;
}



bool impara_path_searcht::has_enabled(const statet& state) 
{
  if(state.atomic_section_count>0)
    return state.threads[state.get_current_thread()].active;

  for(unsigned t=0; t<state.threads.size(); ++t)
    if(enabled(state,t)) return true;

  return false;

}

bool impara_path_searcht::enabled(const statet& state, unsigned t)
{
  return state.threads[t].active;
}


/*******************************************************************\

Function: impara_path_searcht::dot

  Inputs: graph output

 Outputs:

 Purpose:

\*******************************************************************/

void impara_path_searcht::dot_output() 
{

  if(options.get_option("dot")!="")
  {
    std::string out_file(options.get_option("dot"));

    std::ofstream dot_file(out_file.c_str());
    nodes.dot_output(dot_file, error_node);
  }
}

/*******************************************************************\

Function: impara_path_searcht::reset_statistics

  Inputs: graph output

 Outputs:

 Purpose:

\*******************************************************************/


void impara_path_searcht::reset_statistics()
{
  // stop the time
  start_time=current_time();
  close_time=start_time-start_time;
  force_time=start_time-start_time;

  number_of_failed_properties=0;
  number_of_VCCs=0;
  number_of_VCCs_after_simplification=0;

  number_of_uncoverings=0;
  number_of_finished_states=0;
  number_of_dropped_states=0;
  number_of_uncoverings=0;
  number_of_threads=1;
  cover_checks_total=0;
  cover_checks_ok=0;
  cover_checks_syntactic=0;
  cover_checks_syntactic_ok=0;
  cover_checks_smt=0;
  cover_checks_smt_ok=0;
  force_cover_checks_total=0;
  force_cover_checks_ok=0;
  refinements=0;
  assertion_checks=0;
}

/*******************************************************************\

Function: impara_path_searcht::compute_cutpoints

  Inputs: graph output

 Outputs:

 Purpose:

\*******************************************************************/

void impara_path_searcht::compute_cutpoints()
{
  for(loc_reft i=locs.begin(); i!=locs.end(); ++i)
  {
    const loct &loc=locs[i];
    
    if(loc.branch_target.is_nil())
      continue;
    
    cutpoints.insert(loc.branch_target);
  }
}

/*******************************************************************\

Function: path_searcht::initialize_property_map

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void impara_path_searcht::initialize_property_map(
  const goto_functionst &goto_functions)
{
  for(goto_functionst::function_mapt::const_iterator
      it=goto_functions.function_map.begin();
      it!=goto_functions.function_map.end();
      it++)
    if(!it->second.is_inlined())
    {
      const goto_programt &goto_program=it->second.body;
    
      for(goto_programt::instructionst::const_iterator
          it=goto_program.instructions.begin();
          it!=goto_program.instructions.end();
          it++)
      {
        if(!it->is_assert())
          continue;
      
        const source_locationt &source_location=it->source_location;
      
        irep_idt property_name=source_location.get_property_id();
        
        property_entryt &property_entry=property_map[property_name];
        property_entry.status=NOT_REACHED;
        property_entry.description=source_location.get_comment();
      }
    }    
}
