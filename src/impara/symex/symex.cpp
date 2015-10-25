/*******************************************************************\

Module: Concrete Symbolic Transformer

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "impara_symex_class.h"

//#define DEBUG

/*******************************************************************\

Function: symext::assign

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void symext::assign(
  statet &state,
  const exprt &lhs,
  const exprt &rhs)
{
  if(rhs.id()==ID_side_effect) // catch side effects on rhs
  {
    const side_effect_exprt &side_effect_expr=to_side_effect_expr(rhs);
    const irep_idt &statement=side_effect_expr.get_statement();

    if(statement==ID_malloc)
    {
      symex_malloc(state, lhs, side_effect_expr);
      return;
    }
    else if(statement==ID_nondet)
    {
      // done in statet:instantiate_rec
    }
    else
      throw "unexpected side-effect on rhs: "+id2string(statement);
  }

  exprt lhs_address, ssa_lhs;

  try
  {

    // read the address of the lhs, with propagation
    lhs_address=state.read(address_of_exprt(lhs));
  
    // now SSA it, no propagation
    ssa_lhs=
      state.read_no_propagate(dereference_exprt(lhs_address));

  }
  catch(std::string& s)
  {          
		return;
  }

  // read the rhs (NOTE: do propagation if it's a pointer type)
  typet type=state.var_map.ns.follow(ssa_lhs.type());
  bool pointer_type=type.id()==ID_pointer;

  exprt ssa_rhs= pointer_type ? state.read(rhs) : state.read_no_propagate(rhs);

  // start recursion on lhs
  exprt::operandst _guard; // start with empty guard
  assign_rec(state, _guard, ssa_lhs, ssa_rhs);
}

/*******************************************************************\

Function: symext::c_sizeof_type_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

inline static typet c_sizeof_type_rec(const exprt &expr)
{
  const irept &sizeof_type=expr.find(ID_C_c_sizeof_type);

  if(!sizeof_type.is_nil())
  {
    return static_cast<const typet &>(sizeof_type);
  }
  else if(expr.id()==ID_mult)
  {
    forall_operands(it, expr)
    {
      typet t=c_sizeof_type_rec(*it);
      if(t.is_not_nil()) return t;
    }
  }
  
  return nil_typet();
}

void symext::symex_malloc(
  statet &state,
  const exprt &lhs,
  const side_effect_exprt &code)
{
  if(code.operands().size()!=1)
    throw "malloc expected to have one operand";
    
  // increment dynamic object counter
  unsigned dynamic_count=++state.dynamic_count;
  
  exprt size=code.op0();
  typet object_type=nil_typet();
  
  {
    exprt tmp_size=state.read(size); // to allow constant propagation
   
    // special treatment for sizeof(T)*x
    if(tmp_size.id()==ID_mult &&
       tmp_size.operands().size()==2 &&
       tmp_size.op0().find(ID_C_c_sizeof_type).is_not_nil())
    {
      object_type=array_typet(
        c_sizeof_type_rec(tmp_size.op0()),
        tmp_size.op1());      
    }
    else
    {
      typet tmp_type=c_sizeof_type_rec(tmp_size);
      
      if(tmp_type.is_not_nil())
      {
        // Did the size get multiplied?
        mp_integer elem_size=pointer_offset_size(tmp_type, state.var_map.ns);
        mp_integer alloc_size;
        if(elem_size<0 || to_integer(tmp_size, alloc_size))
        {
        }
        else
        {
          if(alloc_size==elem_size)
            object_type=tmp_type;
          else
          {
            mp_integer elements=alloc_size/elem_size;
            
            if(elements*elem_size==alloc_size)
              object_type=array_typet(tmp_type, from_integer(elements, tmp_size.type()));
          }
        }
      }
    }
    
    if(object_type.is_nil())
      object_type=array_typet(unsigned_char_type(), tmp_size);

    // we introduce a fresh symbol for the size
    // to prevent any issues of the size getting ever changed
    
    if(object_type.id()==ID_array &&
       !to_array_type(object_type).size().is_constant())
    {
      exprt &size=to_array_type(object_type).size();
    
      symbolt size_symbol;

      size_symbol.base_name="dynamic_object_size"+i2string(dynamic_count);
      size_symbol.name="symex_dynamic::"+id2string(size_symbol.base_name);
      size_symbol.is_lvalue=true;
      size_symbol.type=tmp_size.type();
      size_symbol.mode=ID_C;

      //state.var_map(size_symbol.name, suffix, size_symbol.type);

      assign(state,
             size_symbol.symbol_expr(), 
             size);

      size=size_symbol.symbol_expr();
    }
  }
  
  // value
  symbolt value_symbol;

  value_symbol.base_name="dynamic_object"+i2string(state.dynamic_count);
  value_symbol.name="symex_dynamic::"+id2string(value_symbol.base_name);
  value_symbol.is_lvalue=true;
  value_symbol.type=object_type;
  value_symbol.type.set("#dynamic", true);
  value_symbol.mode=ID_C;

  //state.var_map(value_symbol.name, suffix, value_symbol.type);

  address_of_exprt rhs;
  
  if(object_type.id()==ID_array)
  {
    rhs.type()=pointer_typet(value_symbol.type.subtype());
    index_exprt index_expr(value_symbol.type.subtype());
    index_expr.array()=value_symbol.symbol_expr();
    index_expr.index()=gen_zero(index_type());
    rhs.op0()=index_expr;
  }
  else
  {
    rhs.op0()=value_symbol.symbol_expr();
    rhs.type()=pointer_typet(value_symbol.type);
  }
  
  if(rhs.type()!=lhs.type())
    rhs.make_typecast(lhs.type());

  #ifdef DEBUG
  std::cout << "symex_malloc " << from_expr(state.var_map.ns, "", rhs) 
            << " " << rhs.type().pretty() << std::endl;
  #endif
  
  assign(state, lhs, rhs);
}


/*******************************************************************\

Function: symext::assign_rec_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void symext::assign_rec_symbol(
  statet &state,
  exprt::operandst &guard, 
  const symbol_exprt &symbol_expr, 
  const exprt &ssa_rhs)
{
  state.record_assign(
    guard, symbol_expr, ssa_rhs, state.get_current_thread());
}

/*******************************************************************\

Function: symext::assign_rec_index

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void symext::assign_rec_index(
  statet &state,
  exprt::operandst &guard, 
  const index_exprt &ssa_lhs_index_expr, 
  const exprt &ssa_rhs)
{
  #ifdef SPLIT_DATA
  throw "unexpected array index on lhs";    
  #endif
  
  #ifdef WITH_DATA     
  const exprt &array_expr=ssa_lhs_index_expr.array();
  const typet &lhs_type=state.var_map.ns.follow(array_expr.type());
  const exprt &index=ssa_lhs_index_expr.index();
  exprt new_rhs=exprt(ID_with, lhs_type);

  exprt rhs=ssa_rhs;
  if(lhs_type.subtype()!=ssa_rhs.type())
  { 
    rhs=typecast_exprt(ssa_rhs, lhs_type.subtype());
  }
   
  new_rhs.copy_to_operands(array_expr, index, rhs);

  assign_rec(state, guard, array_expr, new_rhs);  
  #endif
}

/*******************************************************************\

Function: symext::assign_rec_member

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void symext::assign_rec_member(
  statet &state,
  exprt::operandst &guard, 
  const member_exprt &ssa_lhs_member_expr, 
  const exprt &ssa_rhs)
{

  #ifdef WITH_DATA
  exprt struct_expr=ssa_lhs_member_expr.struct_op();
  typet struct_type=state.var_map.ns.follow(struct_expr.type());  

  const irep_idt &component_name=ssa_lhs_member_expr.get_component_name();

  exprt new_rhs(ID_with, struct_type);
  new_rhs.copy_to_operands(struct_expr, exprt(ID_member_name), ssa_rhs);
  new_rhs.op1().set(ID_component_name, component_name);

  assign_rec(state, guard, struct_expr, new_rhs);    
  #endif   
    
  #ifdef SPLIT_DATA    
  const exprt &struct_op=ssa_lhs_member_expr.struct_op();

  const typet &compound_type=
    state.var_map.ns.follow(struct_op.type());

  if(compound_type.id()==ID_struct)
  {
    throw "unexpected struct member on lhs" + ssa_lhs_member_expr.pretty();    
  }
  else if(compound_type.id()==ID_union)
  {
    // adjust the rhs
    union_exprt new_rhs;
    new_rhs.type()=struct_op.type();
    new_rhs.set_component_name(ssa_lhs_member_expr.get_component_name());
    new_rhs.op()=ssa_rhs;
    
    assign_rec(state, guard, struct_op, new_rhs);
  }
  else
    throw "assign_rec: member expects struct or union type";
  #endif  
    
}

/*******************************************************************\

Function: symext::assign_rec_struct

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void symext::assign_rec_struct(
  statet &state,
  exprt::operandst &guard, 
  const struct_exprt &ssa_lhs_struct_expr, 
  const exprt &ssa_rhs)
{
  #ifdef SPLIT_DATA
  const struct_typet &struct_type=
    to_struct_type(state.var_map.ns.follow(ssa_lhs_struct_expr.type()));
  const struct_typet::componentst &components=
    struct_type.components();
  
  // split up into components
  const exprt::operandst &operands=ssa_lhs_struct_expr.operands();
  
  assert(operands.size()==components.size());
  
  for(unsigned i=0; i<components.size(); i++)
  {
    exprt new_rhs=
      ssa_rhs.is_nil()?ssa_rhs:
      simplify_expr(member_exprt(ssa_rhs, components[i].get_name(), components[i].type()),
        state.var_map.ns);
    assign_rec(state, guard, operands[i], new_rhs);
  }
  #endif
}


/*******************************************************************\

Function: symext::assign_rec_byte_extract

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void symext::assign_rec_byte_extract(
  statet &state,
  exprt::operandst &guard, 
  const byte_extract_exprt &byte_extract_expr, 
  const exprt &ssa_rhs)
{
  // assignment to byte_extract operators:
  // turn into byte_update operator
  
  irep_idt new_id;
  
  if(byte_extract_expr.id()==ID_byte_extract_little_endian)
    new_id=ID_byte_update_little_endian;
  else if(byte_extract_expr.id()==ID_byte_extract_big_endian)
    new_id=ID_byte_update_big_endian;
  else
    assert(false);

  if(byte_extract_expr.op().type().id()==ID_array) // NOTE: deal with unbounded arrays
  {
    const array_typet &array_type=to_array_type(byte_extract_expr.op().type());

    if(!array_type.size().is_constant())
    {
      const exprt &lhs_array=byte_extract_expr.op();
      const exprt &lhs_index=byte_extract_expr.offset();
      const typet &lhs_type=byte_extract_expr.op().type();
    
      if(lhs_type.id()!=ID_array && lhs_type.subtype()==byte_extract_expr.type())
        throw "index must take array type operand, but got `"+
          lhs_type.id_string()+"'\n in expr " + byte_extract_expr.pretty(2) + "\n";
    
      exprt new_rhs(ID_with, lhs_type);
      new_rhs.copy_to_operands(lhs_array, lhs_index, ssa_rhs);
       
      assign_rec(state, guard, lhs_array, new_rhs);
      return;
    }
  }
  else
  {
    byte_update_exprt new_rhs(new_id);

    new_rhs.type()=byte_extract_expr.op().type();
    new_rhs.op()=byte_extract_expr.op();
    new_rhs.offset()=byte_extract_expr.offset();
    new_rhs.value()=ssa_rhs;
    
    const exprt new_lhs=byte_extract_expr.op();

    #ifdef DEBUG
    std::cout << "assign_rec_byte_extract " << from_expr(new_lhs) << " := " << from_expr(new_rhs) << std::endl;
    #endif

    assign_rec(state, guard, new_lhs, new_rhs);
  }
}

/*******************************************************************\

Function: symext::assign_rec_array

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void symext::assign_rec_array(
  statet &state,
  exprt::operandst &guard, 
  const array_exprt &ssa_lhs_array_expr, 
  const exprt &ssa_rhs)
{
  #ifdef SPLIT_DATA
  const typet &ssa_lhs_type=state.var_map.ns.follow(ssa_lhs_array_expr.type());

  if(ssa_lhs_type.id()!=ID_array)
    throw "array constructor must have array type";
    
  const array_typet &array_type=
    to_array_type(ssa_lhs_type);
    
  const exprt::operandst &operands=ssa_lhs_array_expr.operands();
  
  // split up into elements
  for(unsigned i=0; i<operands.size(); i++)
  {
    exprt new_rhs=
      ssa_rhs.is_nil()?ssa_rhs:
      simplify_expr(index_exprt(ssa_rhs, from_integer(i, index_type()), array_type.subtype()),
        state.var_map.ns);
    assign_rec(state, guard, operands[i], new_rhs);
  }
  #endif
}

/*******************************************************************\

Function: symext::assign_rec_vector

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void symext::assign_rec_vector(
  statet &state,
  exprt::operandst &guard, 
  const vector_exprt &ssa_lhs_vector_expr, 
  const exprt &ssa_rhs)
{  
  #ifdef SPLIT_DATA
  const vector_typet &vector_type=
    to_vector_type(state.var_map.ns.follow(ssa_lhs_vector_expr.type()));
  
  const exprt::operandst &operands=ssa_lhs_vector_expr.operands();
  
  // split up into elements
  for(unsigned i=0; i<operands.size(); i++)
  {
    exprt new_rhs=
      ssa_rhs.is_nil()?ssa_rhs:
      simplify_expr(index_exprt(ssa_rhs, from_integer(i, index_type()), vector_type.subtype()),
        state.var_map.ns);
    assign_rec(state, guard, operands[i], new_rhs);
  }
  #endif
}

/*******************************************************************\

Function: symext::assign_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void symext::assign_rec(
  statet &state,
  exprt::operandst &guard, 
  const exprt &ssa_lhs, 
  const exprt &ssa_rhs)
{
  //const typet &ssa_lhs_type=state.var_map.ns.follow(ssa_lhs.type());
    
  if(ssa_lhs.id()==ID_symbol)
  {   
    const symbol_exprt &symbol_expr=to_symbol_expr(ssa_lhs);
    
    assign_rec_symbol(state, guard, symbol_expr, ssa_rhs);
  }
  else if(ssa_lhs.id()==ID_member)
  {
    const member_exprt &ssa_lhs_member_expr=to_member_expr(ssa_lhs);

    assign_rec_member(state, guard, ssa_lhs_member_expr, ssa_rhs);
  }
  else if(ssa_lhs.id()==ID_index)
  {
    const index_exprt &ssa_lhs_index_expr=to_index_expr(ssa_lhs);

    assign_rec_index(state, guard, ssa_lhs_index_expr, ssa_rhs);
  }
  else if(ssa_lhs.id()==ID_dereference)
  {
  
    const goto_programt::instructiont &instruction=
      *state.get_instruction();
 
    std::cout << "Warning: failed dereference "
              << instruction.source_location.as_string() << std::endl
              << as_string(state.var_map.ns, *state.get_instruction()) << std::endl; 
    /*
 
    throw "unexpected dereference on lhs \n"
         + instruction.source_location.as_string() + "\n"
         + as_string(state.var_map.ns, *state.get_instruction()) + "\n" 
         + from_expr(state.var_map.ns, "", ssa_lhs) + " := " 
         + from_expr(state.var_map.ns, "", ssa_rhs);
    */
  }
  else if(ssa_lhs.id()==ID_if)
  {
    const if_exprt &lhs_if_expr=to_if_expr(ssa_lhs);
    exprt cond=lhs_if_expr.cond();

    // true
    guard.push_back(cond);
    assign_rec(state, guard, lhs_if_expr.true_case(), ssa_rhs);
    guard.pop_back();
    
    // false
    guard.push_back(not_exprt(cond));
    assign_rec(state, guard, lhs_if_expr.false_case(), ssa_rhs);
    guard.pop_back();
  }
  else if(ssa_lhs.id()==ID_byte_extract_little_endian ||
          ssa_lhs.id()==ID_byte_extract_big_endian)
  {
    const byte_extract_exprt &byte_extract_expr=
      to_byte_extract_expr(ssa_lhs);

    assign_rec_byte_extract(state, guard, byte_extract_expr, ssa_rhs);
  }
  else if(ssa_lhs.id()==ID_struct)
  {
    const struct_exprt &ssa_lhs_struct_expr=to_struct_expr(ssa_lhs);

    assign_rec_struct(state, guard, ssa_lhs_struct_expr, ssa_rhs);
  }
  else if(ssa_lhs.id()==ID_array)
  {
    const array_exprt &ssa_lhs_array_expr=to_array_expr(ssa_lhs);

    assign_rec_array(state, guard, ssa_lhs_array_expr, ssa_rhs);
  }
  else if(ssa_lhs.id()==ID_vector)
  {
    const vector_exprt &ssa_lhs_vector_expr=to_vector_expr(ssa_lhs);

    assign_rec_vector(state, guard, ssa_lhs_vector_expr, ssa_rhs);
  }
  else if(ssa_lhs.id()==ID_typecast)
  {
    assign_rec(state, guard, ssa_lhs.op0(), ssa_rhs);
  }
  else if(ssa_lhs.id()==ID_string_constant ||
          ssa_lhs.id()=="NULL-object" ||
          ssa_lhs.id()=="zero_string" ||
          ssa_lhs.id()=="is_zero_string" ||
          ssa_lhs.id()=="zero_string_length")
  {
    // ignore
  }
  else
  {

		// throw "symext::assign_rec(): unexpected lhs: "+ssa_lhs.id_string();
  }
}

/*******************************************************************\

Function: symext::function_call_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void symext::function_call_rec(
  statet &state,
  const code_function_callt &call,
  const exprt &function,
  std::list<statet> &further_states)
{
  #ifdef DEBUG
  std::cout << "function_call_rec: " << function.pretty() << std::endl;
  #endif

  if(function.id()==ID_symbol)
  {
    const irep_idt &function_identifier=
      to_symbol_expr(function).get_identifier();

    // find the function
    locst::function_mapt::const_iterator f_it=
      state.locs.function_map.find(function_identifier);

    if(f_it==state.locs.function_map.end())
      throw "failed to find `"+id2string(function_identifier)+"' in function_map";
  
    const locst::function_entryt &function_entry=f_it->second;

    loc_reft function_entry_point=function_entry.first_loc;
  
    // do we have a body?
    if(function_entry_point==loc_reft())
    {
      // no body, this is a skip, assign non-deterministic return value
      if(call.lhs().is_not_nil())
        assign(state, call.lhs(), side_effect_exprt(ID_nondet, call.lhs().type()));

      state.next_pc();
      return;
    }
  
    // push a frame on the call stack
    statet::threadt &thread=state.threads[state.get_current_thread()];
    thread.call_stack.push_back(statet::framet());
    statet::framet &frame=thread.call_stack.back();
    frame.current_function=function_identifier;
    frame.return_location=thread.pc.next_loc();
    frame.return_lhs=call.lhs();
    
    // update statistics
    state.recursion_map[function_identifier]++;

    const code_typet &code_type=function_entry.type;


    const code_typet::parameterst &function_parameters=code_type.parameters();

    const exprt::operandst &call_arguments=call.arguments();
      
    // now assign the argument values
    for(unsigned i=0; i<call_arguments.size(); i++)
    {
      if(i<function_parameters.size())
      {
      
        const code_typet::parametert &function_parameter=function_parameters[i];
        irep_idt identifier=function_parameter.get_identifier();
  
        if(identifier==irep_idt())
          throw "function_call " + id2string(function_identifier) + " no identifier for function argument";

        symbol_exprt lhs(identifier, function_parameter.type());
            
        // assign parameters and handle save+restore
        assign_save_frame(state, lhs, call_arguments[i]);
      }
    }

    // set the new PC
    thread.pc=function_entry_point;
  }
  else if(function.id()==ID_dereference)
  {
    // should not happen, we read() before
    throw "function_call_rec got dereference";
  }
  else if(function.id()==ID_if)
  {
    const if_exprt &if_expr=to_if_expr(function);
    exprt guard=if_expr.cond();
    
    // add a 'further state' for the false-case
    
    {
      further_states.push_back(state);
      statet &false_state=further_states.back();
      exprt negated_guard=not_exprt(guard);      
      false_state.record_assume(negated_guard);
      function_call_rec(further_states.back(), call, if_expr.false_case(), further_states);
    }

    // do the true-case in 'state'
    {
      state.record_assume(guard);
      function_call_rec(state, call, if_expr.true_case(), further_states);
    }
  }
  else
    throw "TODO: function_call "+function.id_string();
}

/*******************************************************************\

Function: symext::return_from_function

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void symext::return_from_function(
  statet &state,
  const exprt &return_value)
{
  statet::threadt &thread=state.threads[state.get_current_thread()];

  // returning from very last function?
  if(thread.call_stack.empty())
  {
    state.disable_current_thread();
  }
  else
  {
    // update statistics
    state.recursion_map[thread.call_stack.back().current_function]--;
  
    // set PC to return location
    thread.pc=thread.call_stack.back().return_location;

    // return variable
    const exprt &return_lhs=thread.call_stack.back().return_lhs;

    // assign the return value
    if(return_value.is_not_nil() &&
       thread.call_stack.back().return_lhs.is_not_nil())
      assign(state, return_lhs, return_value);

    state.pop_frame(return_lhs);
  }
}

/*******************************************************************\

Function: symext::do_goto

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void symext::do_goto(
  statet &state,
  std::list<statet> &further_states)
{
  const goto_programt::instructiont &instruction=
    *state.get_instruction();

  if(instruction.is_backwards_goto())
  {
    // we keep a statistic on how many times we execute backwards gotos
    state.unwinding_map[state.pc()]++;
  }

  exprt guard=state.read_no_propagate(instruction.guard); // NOTE: read in path_symex
  
  if(guard.is_true())
  {
    state.record_goto(guard, true);
    return; // we are done
  }

  if(!guard.is_false())
  {
    // branch taken case
    // copy the state into 'further_states'
    further_states.push_back(state);
    statet &further_state=further_states.back();
    further_state.record_goto(guard, true);
  }

  // branch not taken case
  exprt negated_guard=not_exprt(guard);
  state.record_goto(negated_guard, false);
}

/*******************************************************************\

Function: symext::do_goto

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void symext::do_goto(
  statet &state,
  bool taken)
{
  const goto_programt::instructiont &instruction=
    *state.get_instruction();

  if(instruction.is_backwards_goto())
  {
    // we keep a statistic on how many times we execute backwards gotos
    state.unwinding_map[state.pc()]++;
  }

  exprt guard=state.read_no_propagate(instruction.guard);
  
  if(taken)
  {
    // branch taken case
    state.record_goto(guard, true);
  }
  else
  {
    // branch not taken case
    exprt negated_guard=not_exprt(guard);
    state.record_goto(negated_guard, false);
  }
}

/*******************************************************************\

Function: symext::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void symext::operator()(
  statet &state,
  std::list<statet> &further_states)
{
  const goto_programt::instructiont &instruction=
    *state.get_instruction();
    
  #ifdef DEBUG
  std::cout << "symext::operator(): " 
            << "N" << state.node_ref->number
            << " " << as_string(state.var_map.ns, instruction)
            << std::endl;
  #endif

  switch(instruction.type)
  {
  case END_FUNCTION:
    // pop the call stack
    state.record_step();
    return_from_function(state, nil_exprt());
    break;
    
  case RETURN:
    // pop the call stack
    {
      state.record_step();
      exprt return_val=instruction.code.operands().size()==1?
                       instruction.code.op0():nil_exprt();
      return_from_function(state, return_val);
    }
    break;
    
  case START_THREAD:
    {
      const loct &loc=state.locs[state.pc()];
      assert(!loc.branch_target.is_nil());
      
      state.record_step();
      
      state.next_pc();
      
      // ordering of the following matters due to vector instability
      unsigned new_thread_id=state.threads.size();
      statet::threadt &new_thread=state.add_thread();

      statet::threadt &old_thread=state.threads[state.get_current_thread()];
      new_thread.pc=loc.branch_target;
      
      // copy over local variables to new_thread
      for(statet::var_valt::const_iterator
          var_it=old_thread.local_vars.begin();
          var_it!=old_thread.local_vars.end();
          ++var_it)
      {
        const symbol_exprt ssa_rhs=var_it->ssa_symbol;
        
        if(ssa_rhs.id()!=ID_symbol)
          continue;
        
        symbol_exprt symbol_expr=to_symbol_expr(from_ssa(ssa_rhs));
        irep_idt identifier=symbol_expr.get_identifier();
        
        
        if(identifier==irep_idt())
          continue;
        
        impara_var_mapt::var_infot &var_info=
          state.var_map(identifier, "", symbol_expr.type());
        
        if(new_thread.local_vars.size()<=var_info.number) 
          new_thread.local_vars.resize(var_info.number+1);
        
        symbol_exprt
          ssa_lhs=var_info.ssa_symbol(
            new_thread_id, state.get_depth());

        statet::var_statet &var_state=new_thread.local_vars[var_info.number];
        var_state.ssa_symbol=ssa_lhs;
        var_state.value=var_it->value;  
        
        exprt::operandst guard;

        state.record_assign(
          guard, ssa_lhs, ssa_rhs, new_thread_id);

      }
      state.record_thread_init();
    }
    break;
    
  case END_THREAD:
    state.record_step();
    state.disable_current_thread();
    break;
    
  case GOTO:
    do_goto(state, further_states);
    break;
    
  case CATCH:
    // ignore for now
    state.record_step();
    state.next_pc();
    break;
    
  case THROW:
    state.record_step();
    throw "THROW not yet implemented";
    
  case ASSUME:
    
    if(instruction.guard.is_false())
    {
      state.record_assume(instruction.guard);
    }
    else
    {
      exprt guard=state.read_no_propagate(instruction.guard);
      state.record_assume(guard);
    }
    state.next_pc();
    break;
      
  case ASSERT:
    state.record_assert(state.read_no_propagate(instruction.guard));
    state.next_pc();  
    break;  
  
  case SKIP:
  case LOCATION:
    state.record_step();
    state.next_pc();
    break;
  
  
  case DEAD:
    state.record_step();
    state.next_pc();

    {
      const irep_idt &irep=to_code_dead(instruction.code).get_identifier();
      impara_var_mapt::var_infot &var_info=state.var_map[irep];
      statet::var_statet &var_state=state.get_var_state(var_info);
      var_state.ssa_symbol.make_nil();
      var_state.value.make_nil();
    }

    break;

  case DECL:
    // assigning an RHS of NIL means 'nondet'
    assign_save_frame(state, to_code_decl(instruction.code).symbol(), nil_exprt());
    state.next_pc();
    break;

  case ATOMIC_BEGIN:
    state.record_atomic_begin();
    state.next_pc();
    break;

  case ATOMIC_END:
    state.record_atomic_end();
    state.next_pc();
    break;
    
  case ASSIGN:
    assign(state, to_code_assign(instruction.code));
    state.next_pc();
    break;
    
  case FUNCTION_CALL:
    state.record_step();
    function_call(state, to_code_function_call(instruction.code), further_states);
    break;
    
  case OTHER:
    state.record_step();

    {
      const codet &code=instruction.code;
      const irep_idt &statement=code.get_statement();

      if(statement==ID_expression)
      {
        // like SKIP
      }
      else if(statement==ID_printf)
      {
        // ignore for now (should record stuff printed)
      }
      else if(statement==ID_asm)
      {
        // ignore for now
      }
      else if(statement==ID_fence)
      {
        // ignore for SC
      }
      else {
        // unexpected statement
      }
    }

    state.next_pc();
    break;

  default:
    throw "symext: unexpected instruction";
  }
}

/*******************************************************************\

Function: symext::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void symext::operator()(statet &state)
{
  std::list<statet> further_states;
  operator()(state, further_states);
  if(!further_states.empty())
    throw "symext got unexpected further states";
}

/*******************************************************************\

Function: path_symex

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void impara_symex(
  statet &state,
  std::list<statet> &further_states)
{
  #ifdef DEBUG
  std::cout << "impara_symex: " 
            << std::endl;
  #endif

  symext symex;
  symex(state, further_states);
}

/*******************************************************************\

Function: path_symex

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void impara_symex(statet &state)
{
  symext path_symex;
  path_symex(state);
}

/*******************************************************************\

Function: path_symex_goto

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void impara_symex_goto(
  statet &state,
  bool taken)
{
  symext path_symex;
  path_symex.do_goto(state, taken);
}

/*******************************************************************\

Function: path_symex_assert_fail

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void impara_assert_fail(statet &state)
{
  symext path_symex;
  path_symex.do_assert_fail(state);
}

