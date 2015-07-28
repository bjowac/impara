/*******************************************************************\

Module: Unwound CFG Nodes

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_IMPARA_NODES_H
#define CPROVER_IMPARA_NODES_H

#include "node.h"
#include "node_utils.h"

class node_equiv_classt
{
public:
  node_equiv_classt(const locst &locs, const global_vectort&);

  node_containert node_container;

  void set_pc_vector_ptr(const global_vectort& __global_vector) { global_vector=&__global_vector; }
  const global_vectort* global_vector;

  size_t size() const { return node_container.size(); }

private:
  friend class nodet;
};


inline nodet &node_reft::get() const
{
  assert(node_equiv_class!=0);
  assert(!is_nil());
  return node_equiv_class->node_container[index];
}


inline nodet &node_reft::operator*() const 
{ 
  return get(); 
}

inline nodet *node_reft::operator->() const { 
  return &get(); 
}

inline node_reft &node_reft::operator--()
{
  *this=get().predecessor;
  return *this;
}

inline bool node_reft::operator<(const node_reft &other) const
{
  if(is_nil() || other.is_nil())
    return false;
 
  return get().number < other.get().number;
}

inline void node_reft::generate_successor(
  node_equiv_classt &_node_equiv_class)
{

  node_reft old=*this;

  node_equiv_class=&_node_equiv_class;
  node_containert &node_container=_node_equiv_class.node_container;
 
  index=node_container.size();

  node_container.resize(index+1);
  
  node_container.back().predecessor=old;
}



class nodest
{
public:  
  // Access nodes per LOC^THREADS.
  // The addresses of the lists also need to be stable.
  typedef hash_map_cont<global_vectort, 
                        node_equiv_classt, 
                        global_vector_hasht,
                        global_vector_equalityt> node_mapt;

  typedef std::pair<global_vectort, node_equiv_classt> node_map_entryt;
  node_mapt node_map;

  global_vectort global_vector;
  
  node_reft &new_node(class statet &state)
  {
    state.get_global_pc(global_vector);

    node_mapt::iterator nm_it=node_map.find(global_vector);
		
    if(nm_it == node_map.end())
    {
      node_map_entryt entry(global_vector,
                            node_equiv_classt(locs,global_vector));
      nm_it = node_map.insert(entry).first;
      nm_it->second.set_pc_vector_ptr(nm_it->first);
    }
    
    node_equiv_classt &node_equiv_class=nm_it->second;
      
    state.node_ref.generate_successor(node_equiv_class);

    nodet &node=*state.node_ref;

    node.no_interleavings=state.get_no_thread_interleavings();

    node.number=node_counter;
    node.history=state.history;
    node.thread_nr=state.get_current_thread();
	  	 	  
    ++node_counter;

    return state.node_ref;
  }
  
  unsigned node_counter;
  const locst &locs;
  
  nodest(const locst &__locs, const namespacet& __ns)
   : node_counter(0),
     locs(__locs),
     ns(__ns)
  {
  }

  void dot_output(std::ostream& out, node_reft error_node=node_reft());
  void dot_output(std::ostream& out, std::set<unsigned>& visible);  

protected:
  const namespacet &ns;
};

#endif
