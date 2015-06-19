/*******************************************************************\

Module: Build Goto Trace from State History

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "from_ssa.h"
#include "build_goto_trace.h"

#include <iostream>

#define DEBUG

#ifdef DEBUG
#include <iostream>
#endif

/*******************************************************************\

Function: build_goto_trace

  Inputs:

 Outputs:

 Purpose: follow state history to build a goto trace

\*******************************************************************/

void build_goto_trace(
  const statet &state,
  const decision_proceduret &decision_procedure,
  goto_tracet &goto_trace)
{
  // follow the history in the state
  typedef std::vector<impara_step_reft> stepst; 
  stepst steps;
  steps.reserve(state.get_depth());

  state.history.build_history(steps);

  for(int i=steps.size()-1; i >= 0; --i)
  {
    const impara_stept &step=*steps[i];
  
    goto_trace_stept trace_step;
    
    assert(!step.pc.is_nil());
    trace_step.pc=state.locs[step.pc].target;
    trace_step.thread_nr=step.thread_nr;
    trace_step.step_nr=steps.size()-i-1;
    
    const goto_programt::instructiont &instruction=*trace_step.pc;
    
    bool record=true;
    
    switch(instruction.type)
    {  
    case ASSIGN:
      trace_step.type=goto_trace_stept::ASSIGNMENT;
      trace_step.full_lhs=from_ssa(step.full_lhs);

      record=step.full_lhs.is_not_nil();
      
      if(record)
      {
        trace_step.full_lhs_value=decision_procedure.get(step.ssa_lhs);
        record=record && trace_step.full_lhs_value.id() != ID_symbol;
      }
      break;
    
    case DECL:
      trace_step.type=goto_trace_stept::DECL;
      trace_step.full_lhs=from_ssa(step.full_lhs);

      record=step.full_lhs.is_not_nil();
      
      if(record)
      {          
        trace_step.lhs_object=to_symbol_expr(step.full_lhs);
        record=record && trace_step.full_lhs_value.id() != ID_symbol;
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
      break;
    
    case END_FUNCTION:
      trace_step.type=goto_trace_stept::FUNCTION_RETURN;
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
      goto_trace.add_step(trace_step);
    }
  }

  // add assertion
  const goto_programt::instructiont &instruction=
    *state.get_instruction();

  goto_trace_stept trace_step;

  trace_step.pc=state.get_instruction();
  trace_step.thread_nr=state.get_current_thread();
  trace_step.step_nr=steps.size();
  trace_step.type=goto_trace_stept::ASSERT;

  const irep_idt &comment=
    instruction.source_location.get_comment();

  if(comment!=irep_idt())
    trace_step.comment=id2string(comment);
  else
    trace_step.comment="assertion";

  goto_trace.add_step(trace_step);  

}

