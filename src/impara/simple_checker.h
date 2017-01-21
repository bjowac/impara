/*******************************************************************\

Module: Simplifier

Author: Bjorn Wachter, bjoern.wachter@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_IMPARA_SIMPLE_CHECKER_H
#define CPROVER_IMPARA_SIMPLE_CHECKER_H


#include "symex/state.h"
#include "symex/impara_history.h"
#include "symex/propagation.h"

class simple_checkert 
 {
 public:
   simple_checkert 
   (const locst& __locs,
    const namespacet& __ns,
    impara_step_reft& __history,
    node_reft __ancestor=node_reft()) 
    : propagation(__ns, __history, __ancestor),
      locs(__locs),
      ns(__ns),
      history(__history),
      ancestor(__ancestor)
   {
     propagation.set_hidden(false);
   }
   
   ~simple_checkert()
   {
     propagation.set_hidden(false);
   }

   decision_proceduret::resultt operator()(const exprt& start, const exprt& cond);
 
   propagationt propagation;
 
 protected:
   typedef std::unordered_set<irep_idt, irep_id_hash> symbol_sett;
 
   symbol_sett depends;
   const locst &locs;
   const namespacet& ns;
   impara_step_reft& history;
   node_reft ancestor;
	
   void relevant_assignments();
};

  
#endif
