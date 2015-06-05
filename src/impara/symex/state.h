/*******************************************************************\

Module: State of path-based symbolic simulator

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_IMPARA_STATE_H
#define CPROVER_IMPARA_STATE_H

#include <util/merge_irep.h>
#include <util/replace_expr.h>

#include <path-symex/locs.h>
#include "var_map.h"
#include "impara_history.h"


struct statet
{
public:
  inline statet(
    impara_var_mapt &_var_map,
    const locst &_locs,
    merge_full_irept &_merge_irep,
    impara_historyt &_history):
    var_map(_var_map),
    locs(_locs),
    merge(_merge_irep),
    atomic_section_count(0),
    history(_history),
    current_thread(0),
    no_thread_interleavings(0),
    depth(0),
    nondet_count(0),
    dynamic_count(0),
    replay(false)
  {
  }

  // These are tied to a particular var_map
  // and a particular program.
  impara_var_mapt &var_map;
  const locst &locs;

  merge_full_irept &merge;

  class node_reft node_ref;

  // the value of a variable
  struct var_statet
  {
    // it's a given explicit value or a symbol with given identifier
    exprt value;
    symbol_exprt ssa_symbol;
    
    // for uninterpreted functions or arrays we maintain an index set
    typedef std::set<exprt> index_sett;
    //index_sett index_set;

    var_statet():
      value(nil_exprt()),
      ssa_symbol(irep_idt())
    {
    }
  };
  
  // the values of the shared variables
  typedef std::vector<var_statet> var_valt;
  var_valt shared_vars;
 
  typedef hash_map_cont<irep_idt, var_statet, irep_id_hash> var_state_listt;
 
  // procedure frame
  struct framet
  {
    irep_idt current_function;
    loc_reft return_location;
    exprt return_lhs;
    var_state_listt saved_local_vars;
  };

  // call stack  
  typedef std::vector<framet> call_stackt;
  
  // the state of a thread
  struct threadt
  {
  public:
    loc_reft pc;    
    call_stackt call_stack; // the call stack
    var_valt local_vars; // thread-local variables
    bool active;
    
    threadt():active(true)
    {
    }

    std::set<unsigned> reads, writes;
  };
  
  typedef std::vector<threadt> threadst;
  threadst threads;

  // save + restore
  inline void set_save_frame(bool value) 
  { 
    save_frame=value; 
  }
  
  void save_frame_variable(
    impara_var_mapt::var_infot&, 
    var_statet&);

  void pop_frame(
    const exprt &return_lhs);

  // warning: reference is not stable
  var_statet &get_var_state(
    const impara_var_mapt::var_infot &var_info,
    unsigned thread);
  
  var_statet &get_var_state(
      const impara_var_mapt::var_infot &var_info)
  {
    return get_var_state(var_info, current_thread);
  }


  unsigned atomic_section_count;
  
  inline unsigned get_current_thread() const
  {
    return current_thread;
  }

  inline void set_current_thread(unsigned _thread)
  {
    current_thread=_thread;
  }
  
  void get_global_pc(std::vector<std::vector<loc_reft> > &dest) const;

  goto_programt::const_targett get_instruction() const;
  
  inline bool is_executable() const
  {
    return !threads.empty() &&
           threads[current_thread].active;
  }
  
  inline bool is_active(unsigned thread)
  {
    return thread < threads.size()
        && threads[thread].active;
  }

  inline void swap(statet &other)
  {
    threads.swap(other.threads);
    std::swap(atomic_section_count, other.atomic_section_count);
    std::swap(current_thread, other.current_thread);
    std::swap(no_thread_interleavings, other.no_thread_interleavings);
    std::swap(unwinding_map, other.unwinding_map);
    std::swap(recursion_map, other.recursion_map);
  }

  // execution history
  impara_step_reft history;
  
  // adds an entry to the history
  void record_step();
  
  void record_assume(
    const exprt &guard);
 
  void record_assert(
    const exprt &guard);

  void record_goto(
    const exprt &guard, 
    bool taken);

  void record_assign(
    exprt::operandst &guard, 
    const symbol_exprt &symbol_expr, 
    const exprt &ssa_rhs,
    unsigned thread);

  void record_atomic_begin();

  void record_atomic_end();

  void record_thread_init();

  // various state transformers
  
  inline threadt &add_thread()
  {
    threads.resize(threads.size()+1);
    return threads.back();
  }
  
  inline void disable_current_thread()
  {
    threads[current_thread].active=false;
  }

  inline loc_reft pc() const
  {
    return threads[current_thread].pc;
  }

  inline void next_pc()
  {
    threads[current_thread].pc.increase();
  }

  inline void set_pc(loc_reft new_pc)
  {
    threads[current_thread].pc=new_pc;
  }
  
  inline void set_replay(bool value)
  {
    replay=value;
  }
 
 
  // output  
  void output(std::ostream &out) const;
  void output(const threadt &thread, std::ostream &out) const;

  // instantiate expressions with propagation
  inline exprt read(const exprt &src)
  {
    return read(src, true);
  }
  
  // instantiate without constant propagation
  inline exprt read_no_propagate(const exprt &src)
  {
    return read(src, false);
  }

  exprt dereference_rec(const exprt &src, bool propagate);

  std::string array_index_as_string(const exprt &) const;
  
  // get SSA form of expr (NOTE: not im path_symex)
  exprt ssa_name(const exprt &src, node_reft ancestor) const;

  inline unsigned get_no_thread_interleavings() const
  {
    return no_thread_interleavings;
  }
  
  inline unsigned get_depth() const
  {
    return depth;
  }
  
  bool is_feasible(class decision_proceduret &) const;

  bool check_assertion(class decision_proceduret &);

  // counts how many times we have executed backwards edges
  typedef std::map<loc_reft, unsigned> unwinding_mapt;
  unwinding_mapt unwinding_map;

  unsigned get_no_unwindings();

  // similar for recursive function calls
  typedef std::map<irep_idt, unsigned> recursion_mapt;
  recursion_mapt recursion_map;

  // resolve pointer checks using information from state
  exprt simplify_pointer_checks(const exprt &src);

  exprt simplify_with(const exprt &src);

  bool is_null(const exprt &src) const;

protected:
  unsigned current_thread;
  unsigned no_thread_interleavings;
  unsigned depth;
public:
  unsigned nondet_count;  // free inputs
  unsigned dynamic_count; // memory allocation 
protected:
  bool replay;
  
  bool save_frame;

  exprt read(
    const exprt &src,
    bool propagate);

  exprt instantiate_rec(
    const exprt &src,
    bool propagate);

  exprt instantiate_symbol(
    const symbol_exprt &src,
    const std::string &suffix,
    const typet &final_type,
    bool propagate);

  exprt instantiate_rec_data(
    const exprt &src,
    bool propagate);

  exprt instantiate_rec_address(
    const exprt &src,
    bool propagate);

  exprt read_symbol_member_index(
    const exprt &src,
    bool propagate);
    
  exprt simplify_byte_extract (
    const exprt &src);
    
  bool propagate(const exprt &src);  

  exprt fix_rhs_type(
    const exprt &lhs,
    const exprt &rhs);

  void collect_objects(
    const exprt &src, 
    std::set<exprt> &result);
};

statet initial_state(
  impara_var_mapt &var_map,
  const locst &locs,
  merge_full_irept &merge_irep,
  impara_historyt& history,
  class nodest& nodes,
  class node_reft node);
  
#endif
