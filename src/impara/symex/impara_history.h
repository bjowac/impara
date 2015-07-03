/*******************************************************************\

Module: History for path-based symbolic simulator

Author: Daniel Kroening, kroening@kroening.com
        Bjorn Wachter, bjoern.wachter@gmail.com
        
\*******************************************************************/

#ifndef CPROVER_PATH_SYMEX_HISTORY_H
#define CPROVER_PATH_SYMEX_HISTORY_H

#include <util/std_expr.h>

#include <path-symex/loc_ref.h>

#include "../node_ref.h"

class decision_proceduret;
class impara_stept;
class impara_historyt;

class impara_step_reft
{
public:

  impara_step_reft()
	: history(0),
    index(std::numeric_limits<std::size_t>::max())
  {}

  impara_step_reft(impara_historyt& _history)
	: history(&_history),
    index(std::numeric_limits<std::size_t>::max())
  {}

  void generate_successor();


  exprt rename(const exprt &src, node_reft ancestor) const;

  void writes(const exprt &src, 
                            impara_step_reft until,
                            std::vector<impara_step_reft> &result) const;

  void writes(impara_step_reft until,
              std::set<exprt> &result);
  

  // cone of influence 
  void cone(const exprt &src, 
            impara_step_reft until,
            std::set<exprt> &result);
 
  void add_successor(const impara_step_reft &other);
  
  inline impara_step_reft &operator--();

  inline impara_stept &operator*() const { return get(); }
  inline impara_stept *operator->() const { return &get(); }

  bool is_nil() const
  {
    return index==std::numeric_limits<std::size_t>::max();
  }

  bool operator==(const impara_step_reft &other) const
  {
    return index==other.index;
  }

  bool operator!=(const impara_step_reft &other) const
  {
    return index!=other.index;
  }

  void swap(impara_step_reft &other)
  {
    size_t tmp=index;
  	index=other.index;
	  other.index=tmp;
  }

  inline bool operator<(const impara_step_reft &other) const
  {
    return index < other.index;                
  }

  impara_step_reft &operator=(const impara_step_reft &other)
  {
    history=other.history;
	  index=other.index;
	  return *this;
  }

  void swap(impara_historyt& other);

  // build a forward-traversible version of the history  
  void build_history(std::vector<impara_step_reft> &dest) const;

  // output history as SSA constraints into dest
  void convert(class prop_convt &dest, 
              node_reft ancestor);
 
  // output history as SSA constraints into dest
  void convert(class prop_convt &dest, 
              node_reft ancestor,
              class propagationt &propagation,
              std::vector<class literalt>& literals,
              std::vector<exprt>& lazy,
              std::vector<impara_step_reft> &steps);

  void get_core_steps(class prop_convt &dest, 
            std::vector<class literalt>& literals,
            std::vector<impara_step_reft> &steps);

  // get pre/post symbols 
  void get_symbols(
              std::set<exprt> &input,
              replace_mapt &vars,  
              node_reft ancestor);

  unsigned get_distance(node_reft ancestor);

   // print SSA form of verification condition (NOTE: not im path_symex)
  void output(const namespacet &ns, 
              class propagationt &propagation,  
              node_reft ancestor, const exprt& start, 
              const exprt& cond, std::ostream &out) const;
 
 
   // print SSA form of verification condition (NOTE: not im path_symex)
  void output(const namespacet &ns, 
              const locst &locs,
              class propagationt &propagation,
              node_reft ancestor, const exprt& start, 
              const exprt& cond, std::ostream &out) const;
 
  inline std::size_t get_index() const { return index; }
 
protected:
  impara_historyt* history;
  std::size_t index;
  inline impara_stept &get() const;


  std::string pretty(
    const namespacet &ns, 
    const exprt &expr) const;
};

class impara_stept
{
public:
  impara_step_reft predecessor;

  exprt guard;          
  exprt full_lhs;       
  symbol_exprt ssa_lhs; 
  exprt ssa_rhs;        

  node_reft node_ref;   

  unsigned thread_nr : 12;
  unsigned max_thread : 12; 
  
  loc_reft pc;
  
  inline bool is_hidden() const
  {
    return hidden;
  }

  inline void reset_hidden()
  {
    hidden=false;
  }

  inline void set_assume(bool value=true)
  {
    assume=value;
  }

  inline bool is_assume() const
  {
    return assume;
  }


  inline void set_hidden(bool value=true)
  {
    hidden=value;
  }

  inline bool is_atomic() const
  {
    return atomic;
  }

  inline bool inside_atomic() const
  {
    return atomic_begin || (atomic && !atomic_end);
  }

  inline void set_atomic(bool value=true)
  {
    atomic=value;
  }

  inline void set_atomic_begin(bool value=true)
  {
    atomic_begin=value;
  }

  inline void set_atomic_end(bool value=true)
  {
    atomic_end=value;
  }

  inline void set_thread_init(bool value=true)
  {
    thread_init=value;
  }

  inline bool is_atomic_begin() const
  {
    return atomic_begin;
  }

  inline bool is_atomic_end() const
  {
    return atomic_end;
  }

  enum kindt {
    NON_BRANCH, BRANCH_TAKEN, BRANCH_NOT_TAKEN
  };

  inline void set_branch(
    bool taken)
  {
    branch=true;
    branch_taken=taken;
  }
  
  inline bool is_branch_taken() const
  {
    return branch_taken;
  }

  inline bool is_branch_not_taken() const
  {
    return branch && !branch_taken;
  }

  inline bool is_branch() const
  {
    return branch;
  }

  impara_stept():
    guard(nil_exprt()),
    full_lhs(nil_exprt()),
    ssa_rhs(nil_exprt()),
    thread_nr(0),
    max_thread(0),
    hidden(false),
    assume(false),
    atomic(false),
    atomic_begin(false),
    atomic_end(false),
    branch(false),
    branch_taken(false),
    thread_init(false)
  {
  }
  
  std::string pretty(const namespacet &ns, 
                     const locst &locs,
                     class propagationt &propagation,
                     int step_nr=-1) const;
protected:
  bool hidden         : 1;
  bool assume         : 1;
  bool atomic         : 1;
  bool atomic_begin   : 1;
  bool atomic_end     : 1;
  bool branch         : 1;
  bool branch_taken   : 1;
  bool thread_init    : 1;
};

class impara_historyt
{
public:
  std::vector<impara_stept> step_container;
};

inline impara_stept &impara_step_reft::get() const
{
  assert(history!=0);
  assert(!is_nil());
  return history->step_container[index];
}


inline void impara_step_reft::generate_successor()
{
  impara_step_reft old=*this;
  std::vector<impara_stept> &step_container=history->step_container;
  index=step_container.size();
  step_container.push_back(impara_stept());
  step_container.back().predecessor=old;
}

inline void impara_step_reft::add_successor(const impara_step_reft &other)
{
  generate_successor();
  
  // step that has just been added
  impara_stept &impara_step=history->step_container.back();
  
  // initialise newly added step with other
  impara_step_reft tmp_predecessor=impara_step.predecessor;
  impara_step=*other;
  impara_step.predecessor=tmp_predecessor;
}

inline impara_step_reft &impara_step_reft::operator--()
{
  return *this=get().predecessor;
}

#include <iostream>

inline void impara_step_reft::build_history(
  std::vector<impara_step_reft> &dest) const
{
  impara_step_reft s=*this;

  while(!s.is_nil())
  {
    dest.push_back(s);
    --s;
  }
}

#endif
