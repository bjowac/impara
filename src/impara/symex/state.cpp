/*******************************************************************\

Module: State of path-based symbolic simulator

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/string2int.h>
#include <util/simplify_expr.h>
#include <util/arith_tools.h>
#include <util/byte_operators.h>
#include <util/pointer_offset_size.h>
#include <util/mp_arith.h>
#include <util/expr_util.h>
#include <util/decision_procedure.h>
#include <util/i2string.h>
#include <util/find_symbols.h>
#include <util/replace_expr.h>
#include <util/base_type.h>
#include <util/prefix.h>

#include <goto-symex/rewrite_union.h>
#include <goto-symex/adjust_float_expressions.h>

#include <ansi-c/c_types.h>

#include <pointer-analysis/dereference.h>

#include "state.h"
#include "symex_data_structures.h"

#include "../nodes.h" 

//#define DEBUG

#ifdef DEBUG
#include <iostream>
#include <langapi/language_util.h>
#endif

/*******************************************************************\

Function: initial_state

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

statet initial_state(
  impara_var_mapt &var_map,
  const locst &locs,
  merge_full_irept &merge_full_irep,
  impara_historyt &history,
  class nodest& nodes,
  node_reft node_ref)
{
  statet s(var_map, locs, merge_full_irep, history);
  
  // create one new thread
  statet::threadt &thread=s.add_thread();
  thread.pc=locs.entry_loc; // set its PC
  s.set_current_thread(0);

  if(node_ref.is_nil())
    nodes.new_node(s);
  else
	s.node_ref=node_ref;

  assert(!s.node_ref.is_nil());

  return s;
}

/*******************************************************************\

Function: statet::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

goto_programt::const_targett statet::get_instruction() const
{
  assert(current_thread<threads.size());
  return locs[threads[current_thread].pc].target;
}

/*******************************************************************\

Function: statet::get_global_pc

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void statet::get_global_pc(std::vector<std::vector<loc_reft> > &dest) const
  {
    dest.resize(threads.size());
    for(unsigned thr=0; thr<threads.size(); ++thr)
    {
      std::vector<loc_reft>& dest_call_stack=dest[thr];
      const call_stackt& call_stack=threads[thr].call_stack;
      
      if(threads[thr].active)
      {
      	dest_call_stack.resize(call_stack.size()+1);
       	unsigned i=0;
        for(; i<call_stack.size(); ++i)
      	  dest_call_stack[i]= call_stack[i].return_location;
        dest_call_stack[i]=threads[thr].pc;
      }
      else // assume that the callstack of inactive thread is empty
      { 
        dest_call_stack.resize(1);	
        dest_call_stack[0]=loc_reft();
      }
    }
  }

/*******************************************************************\

Function: statet::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void statet::output(const threadt &thread, std::ostream &out) const
{
  out << "  PC: " << thread.pc << std::endl;
  out << "  Call stack:";
  for(call_stackt::const_iterator
      it=thread.call_stack.begin();
      it!=thread.call_stack.end();
      it++)
  {
    out << " " << it->return_location << std::endl;

    out << "  local vars:\n"; 

    for(var_state_listt::const_iterator
        it1=it->saved_local_vars.begin();
        it1!=it->saved_local_vars.end();
        ++it1)
    {
      out << "   " << it1->first << "\n";
    }        
  }

  out << std::endl;
}

/*******************************************************************\

Function: statet::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void statet::output(std::ostream &out) const
{
  for(unsigned t=0; t<threads.size(); t++)
  {
    out << "*** Thread " << t << std::endl;
    output(threads[t], out);
    out << std::endl;
  }
}

/*******************************************************************\

Function: statet::get_var_state

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

statet::var_statet &statet::get_var_state(
  const impara_var_mapt::var_infot &var_info,
  unsigned thread)
{
  assert(thread<threads.size());

  var_valt &var_val=
    var_info.is_shared()?shared_vars:threads[thread].local_vars;
  if(var_val.size()<=var_info.number) var_val.resize(var_info.number+1);
  return var_val[var_info.number];
}

/*******************************************************************\

Function: statet::record_step

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void statet::record_step()
{
  // update our statistics
  ++depth;

  // is there a context switch happening?
  bool interleaving=
     depth > 1 &&
     !history.is_nil() &&
     history->thread_nr!=current_thread;
     
  if(interleaving)
    no_thread_interleavings++;

  if(replay)
    return;

  // add the step
  history.generate_successor();
  impara_stept &step=*history;

  // copy PC
  assert(current_thread<threads.size());
  step.pc=pc();
  step.thread_nr=current_thread;
  step.max_thread=threads.size()-1;
  step.set_atomic(atomic_section_count);

  step.node_ref=node_ref;
}

/*******************************************************************\

Function: statet::record_boundary

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void statet::record_thread_init()
{
  if(!replay && !history.is_nil())
    history->set_thread_init();
}

/*******************************************************************\

Function: statet::record_assume

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/


void statet::record_assume(const exprt &guard)
{
  record_step();

  if(replay)
    return;

  impara_stept &step=*history;

  if(guard.is_false())
  {
    disable_current_thread();
  }

  step.set_assume();
  //merge ireps
  merge(step.guard);
}


/*******************************************************************\

Function: statet::record_assert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void statet::record_assert(const exprt &guard)
{
  record_step();

  if(replay)
    return;

  impara_stept &step=*history;

  step.guard=guard;
  
  // merge ireps
  merge(step.ssa_rhs);
}

/*******************************************************************\

Function: statet::record_atomic_begin

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void statet::record_atomic_begin()
{
  record_step();

  ++atomic_section_count;

  if(replay)
    return;

  impara_stept &step=*history;

  step.set_atomic_begin();
}


/*******************************************************************\

Function: statet::record_atomic_end

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void statet::record_atomic_end()
{

    
  record_step();

  // defensive
  if(atomic_section_count)
    --atomic_section_count;

  #if 0
  if(!atomic_section_count)
     throw "unmatched ATOMIC_END";
  #endif


  if(replay)
    return;
    
  impara_stept &step=*history;

  step.set_atomic_end();
}

/*******************************************************************\

Function: statet::record_branch

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void statet::record_goto(
  const exprt &guard, 
  bool taken)
{
  const loct &loc=locs[pc()];
  assert(!loc.branch_target.is_nil());

  if(taken)
    set_pc(loc.branch_target);
  else
    next_pc();

  record_assume(guard);

  if(replay)
    return;
    
  impara_stept &step=*history;

  step.guard=guard;

  step.set_branch(taken);
}

/*******************************************************************\

Function: statet::record_assign

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void statet::record_assign(
  exprt::operandst &guard, 
  const symbol_exprt &symbol_expr, 
  const exprt &ssa_rhs,
  unsigned thread)
{
  // These are expected to be SSA symbols
  if(!symbol_expr.get_bool(ID_C_SSA_symbol))
  {
    throw "symext::assign_rec_symbol(): unexpected SSA symbol " 
          + symbol_expr.pretty();
  }

  const irep_idt &full_identifier=symbol_expr.get(ID_C_full_identifier);

  impara_var_mapt::var_infot &var_info=var_map[full_identifier];

  assert(var_info.full_identifier==full_identifier);

  // increase the SSA counter and produce new SSA symbol expression
  symbol_exprt new_lhs=var_info.ssa_symbol(thread, depth+1);

  // record new state of lhs
  {
    // reference is not stable
    statet::var_statet &var_state=get_var_state(var_info, thread);

    // save old value of local variable
    if(var_info.kind.is_procedure_local())
    {
      save_frame_variable(var_info, var_state);
    }
    
    var_state.ssa_symbol=new_lhs;
  }


  exprt new_rhs;

  // rhs nil means non-det assignment
  if(ssa_rhs.is_nil())
  {
    statet::var_statet &var_state=get_var_state(var_info);
    var_state.value=nil_exprt();
    record_step();

    new_rhs=nil_exprt();
  }
  else
  {
    new_rhs=fix_rhs_type(new_lhs, ssa_rhs);
    
    // record the step
    record_step();

    // propagate
    statet::var_statet &var_state=get_var_state(var_info);
    exprt ssa_rhs_prop=instantiate_rec(new_rhs, true);
    exprt value=simplify_expr(ssa_rhs_prop, var_map.ns);
    var_state.value=simplify_with(value); 
  }
  
  if(!replay)
  {
    assert(!history.is_nil()); 
    impara_stept &step=*history;
  
    if(!guard.empty()) 
      step.guard=conjunction(guard);
  
    step.full_lhs=symbol_expr;
    step.ssa_lhs=new_lhs;
    step.ssa_rhs=new_rhs;
    
    // merge ireps
    merge(step.guard);
    merge(step.full_lhs);
    merge(step.ssa_lhs);
    merge(step.ssa_rhs);
  }
}


/*******************************************************************\

Function: statet::fix_rhs_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt statet::fix_rhs_type(const exprt &lhs,
                           const exprt &rhs)
{
  // consistency check
  if(!base_type_eq(rhs.type(), lhs.type(), var_map.ns))
  {    
    return typecast_exprt(rhs, lhs.type());
  }
      
  if(rhs.id()==ID_with) 
  {
    const typet &op0_type=var_map.ns.follow(rhs.op0().type());

    if(op0_type.id()==ID_struct)
    {
      exprt new_rhs=rhs;
    
      with_exprt &with=to_with_expr(new_rhs);
      
      exprt &where=with.where();
      exprt &new_value=with.new_value(); 
    
      const irep_idt &component_name=
        where.get(ID_component_name);

      if(to_struct_type(op0_type).
           has_component(component_name))
      {
        typet component_type=to_struct_type(op0_type).
          component_type(component_name);

        if(!base_type_eq(component_type, new_value.type(), var_map.ns))
        {
          new_value=typecast_exprt(new_value, component_type);
        }
      }
      
      return new_rhs;
    }
  }
  
  return rhs;
}

                      
/*******************************************************************\

Function: symext::propagate

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool statet::propagate(const exprt &src)
{
  if(src.type().id()==ID_pointer)
    return true;

  // propagate things that are 'simple enough'
  if(src.is_constant())
    return true;
  else if(src.id()==ID_member)
    return propagate(to_member_expr(src).struct_op());
  else if(src.id()==ID_index)
    return false;
  else if(src.id()==ID_typecast)
    return propagate(to_typecast_expr(src).op());
  else if(src.id()==ID_symbol)
    return !to_symbol_expr(src).get_bool(ID_C_SSA_symbol) && src.type().id()!=ID_code;
  else if(src.id()==ID_address_of)
    return true;
  else if(src.id()==ID_plus)
  {
    forall_operands(it, src)
      if(!propagate(*it)) return false;
    return true;
  }
  else if(src.id()==ID_array)
  {
    forall_operands(it, src)
      if(!propagate(*it)) return false;
    return true;
  }
  else if(src.id()==ID_vector)
  {
    forall_operands(it, src)
      if(!propagate(*it)) return false;
    return true;
  }
  else if(src.id()==ID_if)
  {
    const if_exprt &if_expr=to_if_expr(src);
    if(!propagate(if_expr.true_case())) return false;
    if(!propagate(if_expr.false_case())) return false;
    return true;
  }
  else if(src.id()==ID_array_of)
  {
    return propagate(to_array_of_expr(src).what());
  }
  else if(src.id()==ID_union)
  {
    return propagate(to_union_expr(src).op());
  }
  else
  {
    return false;
  }
}


/*******************************************************************\

Function: statet::pop_frame

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void statet::pop_frame(
  const exprt &return_lhs)
{
  // restore
  statet::threadt &thread=threads[get_current_thread()];

  var_state_listt &saved_vars=
    thread.call_stack.back().saved_local_vars;

  const irep_idt dummy="";

  const irep_idt &return_identifier=
    return_lhs.id()!=ID_symbol ? 
       dummy
    :  to_symbol_expr(return_lhs).get_identifier(); 
   
  if(false) 
  for(var_state_listt::iterator
      it=saved_vars.begin();
      it!=saved_vars.end();
      ++it)
  {
    impara_var_mapt::var_infot &var_info=var_map[it->first];

    var_statet &var_state=get_var_state(var_info);		

    // don't restore return values
    if(return_identifier != var_info.full_identifier)
    {
      var_state=it->second;
    }
  }

  thread.call_stack.pop_back();
}

/*******************************************************************\

Function: statet::save_frame_variable

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void statet::save_frame_variable(
  impara_var_mapt::var_infot& var_info, 
  var_statet& var_state)
{
  if(!save_frame)
    return;
  
  statet::threadt &thread=threads[get_current_thread()];
  
  irep_idt 
    &full_identifier=var_info.full_identifier;
  
  if(thread.call_stack.empty())
  	return;  
    
  statet::framet 
    &frame=thread.call_stack.back();
  statet::var_state_listt 
    &saved_vars=frame.saved_local_vars;
  statet::var_state_listt::iterator 
    saved_vars_it=saved_vars.find(full_identifier);
  
  if(saved_vars_it==saved_vars.end())
  { 
    std::pair<irep_idt, statet::var_statet> p(full_identifier, var_state);
    saved_vars.insert(p);
  }
}

/*******************************************************************\

Function: statet::get_no_unwindings

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/


unsigned statet::get_no_unwindings()
{
  if(!is_active(current_thread))
    return 0;

  unsigned result=0;

  if(  get_instruction()->is_backwards_goto()
    || get_instruction()->is_function_call())
  {
    for(statet::unwinding_mapt::const_iterator
        it=unwinding_map.begin();
        it!=unwinding_map.end();
        it++)
    {
      result+=it->second;
    }
  }

  return result;
}


