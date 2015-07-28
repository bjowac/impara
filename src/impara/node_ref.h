/*******************************************************************\

Module: Unwound CFG Nodes

Author: Daniel Kroening, kroening@kroening.com
        Bjoern Wachter, bjoern.wachter@gmail.com

\*******************************************************************/

#ifndef CPROVER_IMPARA_NODE_REF_H
#define CPROVER_IMPARA_NODE_REF_H

#include <set>
#include <limits>

class nodet;
class nodest;
class node_equiv_classt;

class node_reft
{
  public:

  explicit inline node_reft(
    class node_equiv_classt &_node_equiv_class,
    std::size_t _index=std::numeric_limits<std::size_t>::max())
    : node_equiv_class(&_node_equiv_class),
	    index(_index)
  {
  }

  inline node_reft():
    node_equiv_class(0), index(std::numeric_limits<std::size_t>::max())
  {
  }

  inline node_equiv_classt &get_node_equiv_class() const
  {
    assert(node_equiv_class!=0);
    return *node_equiv_class;
  }

  inline bool operator==(const node_reft &other) const
  {
    return node_equiv_class == other.node_equiv_class
	    && index == other.index;
  }

  inline bool operator!=(const node_reft &other) const
  {
    return node_equiv_class != other.node_equiv_class
	    || index != other.index;
  }

  inline bool operator<(const node_reft &other) const;
 
  inline void operator=(const node_reft &other)
  {
    node_equiv_class = other.node_equiv_class; 
    index = other.index; 
  }

  inline nodet &operator*() const;

  inline nodet *operator->() const;

  void generate_successor(node_equiv_classt&);

  inline node_reft &operator--();

  node_reft nearest_common_ancestor(const node_reft other) const;

  void leaves(std::vector<node_reft> &dest) const;
 
  unsigned add_cover(node_reft node_ref);
 
  inline bool is_nil() const
  {
    return index==std::numeric_limits<std::size_t>::max();
  }

  inline void make_nil() 
  {
    index=std::numeric_limits<std::size_t>::max();
  }

  typedef std::set<node_reft> sett;
  typedef std::vector<node_reft> listt;

  std::size_t get_index() const { return index; }
  
  void ancestors_same_class(std::vector<node_reft> &result);
  
protected:
   node_equiv_classt *node_equiv_class;
   std::size_t index;

  inline nodet &get() const;

};

#endif
