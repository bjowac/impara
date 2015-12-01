/*******************************************************************\

Module: Build Goto Trace from State History

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <algorithm>

#include <util/simplify_expr.h>
#include "from_ssa.h"
#include "build_goto_trace.h"

#include <iostream>

#define DEBUG

#ifdef DEBUG
#include <iostream>
#endif


// Obtain the identifier from the code
irep_idt getFunctionIdentifier(const goto_programt::instructiont &instruction)
{

  if(instruction.type == FUNCTION_CALL)
  {
 
    const code_function_callt &call = to_code_function_call(instruction.code);
    const exprt &function = call.function();
    
    if(function.id() == ID_symbol)
    {
      irep_idt id = to_symbol_expr(function).get_identifier();
    
      return id;
    }
  }
  
  // Give up
  return irep_idt();
}



/*******************************************************************\

Function: build_goto_trace

  Inputs:

 Outputs:

 Purpose: follow state history to build a goto trace

\*******************************************************************/

void build_goto_trace(
  const statet &state,
  const decision_proceduret &decision_procedure,
  goto_tracet &goto_trace,
  const namespacet &ns)
{
  // follow the history in the state
  typedef std::vector<impara_step_reft> stepst; 
  stepst steps;
  steps.reserve(state.get_depth());

  state.history.build_history(steps);

  std::reverse(steps.begin(), steps.end());

  std::vector< std::vector<irep_idt> > call_stack;
  call_stack.resize(1);

  unsigned step_nr = 0;

  for(unsigned int i=0; i < steps.size(); ++i)
  {
    const impara_stept &step=*steps[i];
  
    goto_trace_stept trace_step;
    
    assert(!step.pc.is_nil());
    trace_step.pc=state.locs[step.pc].target;
    trace_step.thread_nr=step.thread_nr;
    trace_step.step_nr=step_nr;
    
    const goto_programt::instructiont &instruction=*trace_step.pc;

    bool record = !instruction.source_location.get_hide();
    
    switch(instruction.type)
    {  
    case ASSIGN:
      trace_step.type=goto_trace_stept::ASSIGNMENT;
      trace_step.full_lhs=from_ssa(step.full_lhs);

      record=step.full_lhs.is_not_nil();

      if(step.ssa_lhs.id()==ID_symbol)
      {
        std::string 
          id=id2string(to_symbol_expr(step.ssa_lhs).get_identifier());

        // do not report return values or internal symbols      
        if(id.find("#return_value!")!=std::string::npos
           || id.find("__CPROVER")!=std::string::npos)
          record=false;
      }

      if(record)
      {
        trace_step.full_lhs_value=decision_procedure.get(step.ssa_lhs);
        simplify(trace_step.full_lhs_value, ns);
        trace_step.lhs_object_value=decision_procedure.get(step.ssa_lhs);
        trace_step.lhs_object=to_symbol_expr(step.full_lhs);
      }
      break;
    
    case DECL:
      trace_step.type=goto_trace_stept::DECL;
      trace_step.full_lhs=from_ssa(step.full_lhs);

      record=step.full_lhs.is_not_nil();
      
      if(record) {
        trace_step.full_lhs_value=decision_procedure.get(step.ssa_lhs);
        simplify(trace_step.full_lhs_value, ns);
        trace_step.lhs_object_value=decision_procedure.get(step.ssa_lhs);
        trace_step.lhs_object=to_symbol_expr(step.full_lhs);
      }
      break;
      
    case DEAD:
      trace_step.type=goto_trace_stept::DEAD;
      break;
      
    case ASSUME:
      trace_step.type=goto_trace_stept::ASSUME;
      break;
      
    case FUNCTION_CALL:
      trace_step.type=goto_trace_stept::FUNCTION_CALL;
      trace_step.identifier = getFunctionIdentifier(instruction);

      if (step.thread_nr >= call_stack.size()) {
	call_stack.resize(step.thread_nr + 1);
      }

      call_stack[step.thread_nr].push_back(trace_step.identifier);
      break;
    
    case END_FUNCTION:
      trace_step.type=goto_trace_stept::FUNCTION_RETURN;

      if (call_stack.size() > step.thread_nr) {
	if (!call_stack[step.thread_nr].empty()) {
          trace_step.identifier = call_stack[step.thread_nr].back();
	  call_stack[step.thread_nr].pop_back();
	}
      } else {
	trace_step.identifier = "main";
      }

      if (trace_step.identifier == "") {
	record = false;
      }

      break;
      
    case START_THREAD:
      trace_step.type=goto_trace_stept::SPAWN;
      break;
    
    case ATOMIC_BEGIN:
      trace_step.type=goto_trace_stept::ATOMIC_BEGIN;
      break;
    
    case ATOMIC_END:
      trace_step.type=goto_trace_stept::ATOMIC_END;
      break;
    
    default:
      trace_step.type=goto_trace_stept::LOCATION;
    }
  
    if(record)
    {
      ++step_nr;
      goto_trace.add_step(trace_step);
    }
  }

  // add assertion
  const goto_programt::instructiont &instruction=
    *state.get_instruction();

  goto_trace_stept trace_step;

  trace_step.pc=state.get_instruction();
  trace_step.thread_nr=state.get_current_thread();
  trace_step.step_nr=step_nr;
  trace_step.type=goto_trace_stept::ASSERT;

  const irep_idt &comment=
    instruction.source_location.get_comment();

  if(comment!=irep_idt())
    trace_step.comment=id2string(comment);
  else
    trace_step.comment="assertion";

  goto_trace.add_step(trace_step);  

}

