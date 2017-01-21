/*******************************************************************\

Module: 

Author: Bjorn Wachter

\*******************************************************************/

#ifndef CPROVER_IMPARA_DEPENDENCE_CHECK_H
#define CPROVER_IMPARA_DEPENDENCE_CHECK_H

#include <vector>

#include <util/std_expr.h>
#include <symex/var_map.h>
#include <path-symex/locs.h>
#include <symex/impara_history.h>

class dependency_check_baset
{
public:

  typedef std::vector<impara_step_reft> step_cont;

  dependency_check_baset
    (locst &_locs, 
     impara_var_mapt &_var_map, 
     const step_cont &_steps,
     bool _only_pointers) 
    : locs(_locs), 
      var_map(_var_map), 
      steps(_steps),
      only_pointers(_only_pointers) 
      {}
  
  typedef unsigned stept;                              
  typedef std::set<stept> step_sett;
  
  // steps j dependent with i such that i<j
  virtual void operator()(unsigned j, step_sett& dep) { }
  
  locst &locs;
  impara_var_mapt &var_map;  
  
  const step_cont &steps;
  
  bool only_pointers;
};

class dependency_check_coarset : public dependency_check_baset
{
public:
  dependency_check_coarset(locst &_locs, 
                           impara_var_mapt &_var_map, 
                           const step_cont &steps,
                           bool only_pointers);
  
  virtual void operator()(unsigned j, step_sett&);  
   
  /*
   * step_memt ... what shared state is accessed by a step
   * mem_stept ... which steps access a shared state
   */
  
  typedef exprt memt;
  typedef std::set<memt> mem_sett;                   
   
  virtual void operator()(const mem_sett &reads, 
                          const mem_sett& writes, 
                          step_sett&);
 
  typedef std::unordered_map<stept, mem_sett> step_memt;    

  struct accessort
  {
    step_sett reads;
    step_sett writes;
  };

  typedef std::unordered_map<memt, accessort, irep_full_hash, irep_full_eq> 
  mem_stept;

  step_memt step_writes;
  step_memt step_reads;
  mem_stept mem_step;
  
protected:
  void add(const impara_step_reft &step_ref, stept);  
  
  enum rwkindt {READ, WRITE};
  
  void insert_accessor(unsigned i, rwkindt, const mem_sett&, step_sett &dest);
  void insert_accessor(rwkindt, const mem_sett&, step_sett &dest);
  void insert(unsigned i, const step_sett &from, step_sett &dest);

  typedef unsigned thread_idt; 
  typedef std::unordered_map<thread_idt, unsigned> thread_creatort;
  thread_creatort thread_creator;
};

#endif
