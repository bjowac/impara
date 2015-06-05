/*******************************************************************\

Module: Unwound CFG Nodes

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_IMPARA_NODE_H
#define CPROVER_IMPARA_NODE_H

#include <util/merge_irep.h>
#include <util/simplify_expr.h>
#include "node_ref.h"
#include "impara_join.h"


#include <interleaving/dpor/path_summary.h>
#include <interleaving/mpor/dependency_chain.h>
#include <interleaving/utility/sensitivity.h>



#include "symex/impara_history.h"


//#define IMPARA_BIDIR

class nodet
{
public:

  nodet():
    number(unsigned(-1)),
    no_interleavings(0),
    coverings(0),
    label(nil_exprt()),
    refinement(unsigned(-1))
  {
  }

  impara_step_reft history;
   
  class node_reft predecessor;

  #ifdef IMPARA_BIDIR
  node_reft::listt successors;
  #endif

  typedef std::set<unsigned> thread_sett;
  thread_sett expanded_threads;
  
  typedef std::map<unsigned, impara_step_reft> sleep_sett;
  sleep_sett sleep;
  
  path_summaryt path_summary;
  
  dependency_chaint dc;

  static bool subset(const thread_sett& s1, const thread_sett& s2);
  static bool intersect(const thread_sett& s1, const thread_sett &s2); 

  inline bool expanded(unsigned thread)
  {
    return expanded_threads.count(thread);
  }

  void record_expanded(unsigned thread)
  {
    expanded_threads.insert(thread);
  }


  // number in exploration sequence
  unsigned number; 

  unsigned thread_nr;

  unsigned no_interleavings;

  // cover set of this node
  node_reft::listt cover; 

  //#ifdef IMPARA_BIDIR
  node_reft::listt covered_by;
  //#endif
 
  bool is_covered() const;
  
  inline bool is_cover_candidate(nodet &node) const
  {
    return has_label()
	&& !is_covered()
	&& node.dc < dc
	/* && node.no_interleavings >= no_interleavings */;
  }

  bool has_label() const;

  bool operator==(const nodet& other)
  {
    return number == other.number;
  }
  
  const exprt &get_label() { return label; }

  bool refine(const namespacet &ns,
              merge_full_irept &merge,
              unsigned refinements, 
              const exprt &other);

  unsigned coverings;
  
  exprt label;

  // refined in which iteration of refine
  unsigned refinement;

protected:
  friend class node_reft;
  unsigned uncover_all();
};


#endif
