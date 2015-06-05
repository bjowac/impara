/*******************************************************************\

Module: Partial-Order Reduction

Author: Daniel Kroening, kroening@kroening.com
        Bjorn Wachter, bjoern.wachter@gmail.com
        Subodh Sharma, subodh.v.sharma@gmail.com
\*******************************************************************/

#ifndef CPROVER_IMPARA_POR_H
#define CPROVER_IMPARA_POR_H

#include <path-symex/locs.h>

#include "dependency_chain.h"

#include <symex/state.h>

#include <symex/shared.h>

#include <nodes.h>



typedef std::vector<unsigned> interleavingt;

class shared_accesst
{
  public:
 
  shared_accesst(locst& _locs);
  
  void reads_and_writes(statet& state, 
            						std::vector<bool>& is_shared,
            						std::vector<sharedt::sett>& reads, 
            						std::vector<sharedt::sett>& writes);
  
  void rw_sets(statet& state, 
               std::vector<bool>& is_shared,
               std::vector<sharedt::sett>& reads, 
               std::vector<sharedt::sett>& writes);
    
  const goto_programt::instructiont& current_instruction(statet& state, unsigned t);
  
  protected:
    locst& locs;
    
    symbol_exprt thread_symbol(unsigned t);
};



class partial_order_reductiont
{
public:


  partial_order_reductiont(locst& locs,         // program locations
                           statet& state      // current state
                           );

  virtual ~partial_order_reductiont() {}

  virtual void operator()(interleavingt& inter);

  typedef std::list<statet> queuet;
  
  virtual void update(queuet& successors) {}

protected:
  locst &locs;
  statet& state;  
  node_reft parent;
  
  unsigned nr_threads;  
  shared_accesst shared_access; 
  
  std::vector<bool> is_shared;
  std::vector<sharedt::sett> reads;
  std::vector<sharedt::sett> writes;
  
  std::set<unsigned> thread_creators;
  
  bool enabled(statet& state, unsigned t);  
  unsigned local_transition();
  bool is_local(unsigned);

  virtual void interleave(interleavingt& inter, unsigned);
};

class mono_partial_order_reductiont : public partial_order_reductiont
{
public:
  mono_partial_order_reductiont (locst& locs,         // program locations
                                 statet& _state      // current state
                                 );

  typedef std::set<exprt> expr_sett;

	virtual void operator()(interleavingt& inter);

  virtual void update(queuet& successors);
  
protected: 
  void compute_dc(unsigned i);

  std::vector<dependency_chaint> dcs;
  
  virtual void interleave(interleavingt& inter, unsigned);
  
  void print(const sharedt::sett& es);
};



#endif


