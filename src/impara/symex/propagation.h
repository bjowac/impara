/*******************************************************************\

Module: (Limited) propagation

Author: Bjorn Wachter, bjoern.wachter@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_IMPARA_PROPAGATION_H
#define CPROVER_IMPARA_PROPAGATION_H

/* Performs constant-propagation and simplification based on the SSA,
   but limited to SSA steps up until node ancestor.
 */
class propagationt
{ 
public:
  propagationt(const namespacet &__ns);

  propagationt(
              const namespacet &__ns,
              impara_step_reft& __history,
              node_reft __ancestor=node_reft());

  // rewrite dest, if track flag set, marking used SSA steps non-hidden
  exprt operator()(const exprt &dest, bool from_cache=false);

  // rewrite dest, if track flag set, marking used SSA steps non-hidden
  exprt operator()(const exprt &dest, unsigned &cost, bool from_cache=false);

  void assume(const exprt &src);
  
  
  void set_hidden(bool value, bool guards_only=false);
 
  protected:
  // SSA as a map

  void assume_equality(const exprt &src);

  class valuet
  {  
    public:
  
    impara_step_reft step;
    class exprt value;
    unsigned cost;
    
    valuet(const impara_step_reft &_step);
  
    valuet(const exprt &_value);
  };

  typedef hash_map_cont<exprt, valuet, irep_full_hash, irep_full_eq> defst;

  // remember replacements
  typedef std::pair<exprt, unsigned> cache_entryt;
  typedef hash_map_cont<exprt, cache_entryt, irep_full_hash, irep_full_eq> cachet;

  const namespacet &ns;
  impara_step_reft history;
  defst defs;
  cachet cache;

  node_reft ancestor;
  
  // recursive descent into sub-expressions
  bool replace_rec(exprt& dest, unsigned &cost);

  propagationt &operator<<(const impara_step_reft &step_ref);
};

#endif
