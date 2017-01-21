/*******************************************************************\

Module: Concrete Symbolic Transformer

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_IMPARA_SYMEX_CLASS_H
#define CPROVER_IMPARA_SYMEX_CLASS_H

#include <util/arith_tools.h>
#include <util/simplify_expr.h>
#include <util/byte_operators.h>
#include <util/pointer_offset_size.h>
#include <util/expr_util.h>

#include <ansi-c/c_types.h>

#include <pointer-analysis/dereference.h>

#include "from_ssa.h"
#include "symex.h"

#include "symex_data_structures.h"

#ifdef DEBUG
#include "nodes.h"
#include <iostream>
#endif

class symext
{
public:
  inline symext()
  {
  }
  
  void operator()(
    statet &state,
    std::list<statet> &furter_states);

  void operator()(statet &state);

  void do_goto(
    statet &state,
    bool taken);
    
  void do_assert_fail(statet &state)
  {
    const goto_programt::instructiont &instruction=
      *state.get_instruction();

    exprt guard=state.read(not_exprt(instruction.guard));
    state.record_assume(guard);
    state.next_pc();
  }  

protected:
  void do_goto(
    statet &state,
    std::list<statet> &further_states);

  void function_call(
    statet &state,
    const code_function_callt &call,
    std::list<statet> &further_states)
  {
    exprt f=state.read(call.function());
    function_call_rec(state, call, f, further_states);
  }
    
  void function_call_rec(
    statet &state,
    const code_function_callt &function_call,
    const exprt &function,
    std::list<statet> &further_states);
    
  void return_from_function(
    statet &state,
    const exprt &return_value);

  void symex_malloc(
    statet &state,
    const exprt &lhs,
    const side_effect_exprt &code);

  void assign(
    statet &state,
    const exprt &lhs,
    const exprt &rhs);

  inline void assign_save_frame(
    statet &state,
    const exprt &lhs,
    const exprt &rhs)
  {
    state.set_save_frame(true);
    assign(state, lhs, rhs);
    state.set_save_frame(false);
  }

  inline void assign(
    statet &state,
    const code_assignt &assignment)
  {
    assign(state, assignment.lhs(), assignment.rhs());
  }

  void assign_rec(
    statet &state,
    exprt::operandst &guard, // instantiated
    const exprt &ssa_lhs, // instantiated, recursion here
    const exprt &ssa_rhs); // instantiated

  void assign_rec_symbol(
    statet &state,
    exprt::operandst &guard, 
    const symbol_exprt &ssa_lhs, 
    const exprt &ssa_rhs);

  void assign_rec_index(
    statet &state,
    exprt::operandst &guard, 
    const index_exprt &ssa_lhs, 
    const exprt &ssa_rhs);

  void assign_rec_member(
    statet &state,
    exprt::operandst &guard, 
    const member_exprt &ssa_lhs, 
    const exprt &ssa_rhs);
   
  void assign_rec_struct(
    statet &state,
    exprt::operandst &guard, 
    const struct_exprt &ssa_lhs, 
    const exprt &ssa_rhs);

  void assign_rec_byte_extract(
    statet &state,
    exprt::operandst &guard, 
    const byte_extract_exprt &ssa_lhs_byte_extract_expr, 
    const exprt &ssa_rhs);

  void assign_rec_array(
    statet &state,
    exprt::operandst &guard, 
    const array_exprt &ssa_lhs, 
    const exprt &ssa_rhs);

  void assign_rec_vector(
    statet &state,
    exprt::operandst &guard, 
    const vector_exprt &ssa_lhs, 
    const exprt &ssa_rhs);

  static bool propagate(const exprt &src);
};



#endif
