/*******************************************************************\

Module: Forward Path Search

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_IMPARA_PATH_SEARCH_H
#define CPROVER_IMPARA_PATH_SEARCH_H

#include <util/options.h>
#include <util/namespace.h>
#include <solvers/flattening/bv_pointers.h>

#include <goto-programs/safety_checker.h>

#include <path-symex/locs.h>

#include <symex/state.h>
#include <nodes.h>

#include "impara_solver_stats.h"

class impara_path_searcht:public safety_checkert
{
public:
  impara_path_searcht(
    const optionst &_options,
    const namespacet &_ns,
    message_handlert &_message_handler):
    safety_checkert(_ns, _message_handler),
    options        (_options),
    all_properties (false),
    do_cover       (true),
    do_force_cover (true),
    do_propagation (false),
    do_refine_close(true),
    do_simple_force(false),
    do_strengthen  (false),
    do_dpor        (false),    
    do_dpor_pointers (false),
    do_por         (false),
    do_sleep       (false),
    do_eager       (false),
    do_simplify    (true),
    do_bfs         (false),
    do_check_proof (false),	
    do_wordlevel_interpolation(false),
    do_graphml_cex (false),
    do_show_vcc    (false),
    thread_limit   (std::numeric_limits<int>::max()),
    force_limit    (2),
    cover_limit    (std::numeric_limits<int>::max()),
    node_limit     (std::numeric_limits<int>::max()),
    unwind_limit   (std::numeric_limits<int>::max()),
    depth_limit    (std::numeric_limits<int>::max()),
    context_bound  (std::numeric_limits<int>::max()),
    var_map        (_ns),
    locs           (_ns),
    nodes          (locs,_ns)
  {
  }
  
  virtual resultt operator()(
    const goto_functionst &goto_functions);
  
protected:

  friend class impara_parse_optionst;
  class solver_statst;

  // settings and options
  const optionst &options;

  bool all_properties,
       do_assertions,
       do_cover,
       do_force_cover,
       do_propagation,
       do_refine_close,
       do_simple_force,
       do_strengthen,
       do_dpor,
       do_dpor_pointers,
       do_por,
       do_sleep,
       do_eager,
       do_simplify,
       do_bfs,
       do_check_proof,
       do_wordlevel_interpolation,
       do_graphml_cex;
  
  bool do_show_vcc;

  unsigned thread_limit;
  unsigned force_limit;
  unsigned cover_limit;
  unsigned node_limit;
  unsigned unwind_limit;
  unsigned depth_limit;
  unsigned context_bound;


  // variables
  impara_var_mapt var_map;

  // states  
  inline statet initial_state()
  {
    return ::initial_state(var_map, locs, merge, history, nodes, initial_node_ref);
  }
  
  // locations
  locst locs;

  impara_historyt history;
  
  // search
  typedef std::list<statet> queuet;
  queuet queue;    // states to be explored
  
  void search();

  bool has_enabled(const statet& state);
  bool enabled(const statet& state, unsigned thread);


  // DPOR
  typedef std::set<unsigned> thread_sett;
  typedef std::map<node_reft, thread_sett > backtrackt;

  friend class dpor_path_visitort;

  void dpor_search();
  
  void update_sleepset(statet &state);
  unsigned pick_thread(statet& state);
  void compute_backtrack(statet &state, backtrackt &backtrack);
  bool do_backtrack(backtrackt& backtrack);


  queuet::iterator select_state(queuet& queue);

  void expand(statet& state, queuet::iterator& choice);
  bool succ(unsigned t, statet& state, queuet& queue, bool local=false);
  void check_assertion(statet &state);
  
  
  exprt abstract_transformer(statet &state);
  
  // state is exceeding limits
  bool drop_state(statet &state);
  
  // thread is exceeding limits
  bool drop_thread(statet &state);

  typedef std::set<exprt> expr_sett;
  
  struct unsafe_exception
  {
  };
  
  // covering
  nodest nodes;
  node_reft initial_node_ref;

  node_reft pruned_node_ref;

  void set_labels(statet &state);

  bool path_check(statet &state, 
              impara_step_reft &history,
              node_reft ancestor,
              exprt& assumption, 
              exprt& conclusion,
              class simple_checkert &simple_checker,
              impara_solver_statst& solver_stats,
              bool build_trace,
              bool loop);

  bool interpolate(
              statet& state,
              impara_step_reft history,
              node_reft node,
              node_reft ancestor,
              const exprt& start, 
              const exprt& cond);

  bool refine(statet &state, 
              node_reft ancestor,
              const exprt& start, 
              const exprt& cond,
              impara_solver_statst& solver_stats,
              bool build_trace=false,
              bool loop=false);

  bool covered(statet&);

  bool force_cover(statet&, unsigned k);

  typedef hash_map_cont < exprt, bool, irep_hash > expr_bool_maptt;
  expr_bool_maptt implication_table;

  bool close(node_reft);
  bool ancestor_close(node_reft, bool dry_run);
  
  // statistics!
  unsigned number_of_finished_states,
           number_of_dropped_states,
           cover_checks_total, 
           cover_checks_ok, 
           cover_checks_syntactic,
           cover_checks_syntactic_ok,
           cover_checks_smt,
           cover_checks_smt_ok,
     	     refinements,
     	     assertion_checks,
           force_cover_checks_total, 
           force_cover_checks_ok,
					 number_of_uncoverings,
					 number_of_threads;
 
  unsigned number_of_VCCs;
  unsigned number_of_VCCs_after_simplification;
  unsigned number_of_failed_properties;
  
  impara_solver_statst cover_solver_stats,       // cover implication checks
                force_cover_solver_stats, // force-cover checks
                assert_solver_stats,      // assertion checks
                symex_solver_stats;       // path feasibility
 
  absolute_timet start_time;
  
  time_periodt close_time;
  time_periodt force_time;
  time_periodt refine_time;
  time_periodt domain_time;
  time_periodt symex_time;

  void reset_statistics();  
  void print_queue(queuet&);
  void report_statistics();
  void report_limits();


  int decide_branch(statet& state);

  /* status of properties -- when run with all-properties */
  enum statust { NOT_REACHED, PASS, FAIL };

  struct property_entryt
  {
    statust status;
    irep_idt description;
    goto_tracet error_trace;
  };
  
  typedef std::map<irep_idt, property_entryt> property_mapt;
  property_mapt property_map;

protected:

  // avoid dynamic allocation
  queuet successors;
  std::vector<unsigned> threads;

  node_reft error_node;

  void dot_output(); // graph output

  void solver_log_statistics(const satcheckt& satcheck);
  
  struct hash_loc_refst {
     size_t operator()(const loc_reft &loc_ref) const { return loc_ref.loc_number; }
  };
  
  hash_set_cont<loc_reft, hash_loc_refst> cutpoints;
  void compute_cutpoints();
  
	hash_set_cont<std::string> explicit_variables;
  
  void update_explicit_variables(statet &state, unsigned t);
    
  merge_full_irept merge;

  typedef hash_map_cont<exprt, exprt, irep_hash> modelt;

  bool  strengthen(
          statet &state,
          decision_proceduret &sat_dp,
          class simple_checkert &simple_checker,
          node_reft ancestor,
          exprt& assumption, 
          exprt& conclusion,
          impara_solver_statst& solver_stats);

  void get_core_steps(
    impara_step_reft history, 
    node_reft ancestor,     
    std::map<exprt, literalt> &activation,
    bv_pointerst &bv_pointers);


  void get_model(
    decision_proceduret &dp,
    std::set<exprt> &symbols,
    modelt &model);
    
  void initialize_property_map(
    const goto_functionst &goto_functions);      
};

#endif
