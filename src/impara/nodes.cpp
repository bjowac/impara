#include <iostream>
#include <algorithm>

#include <path-symex/locs.h>

#include <symex/state.h>
#include "nodes.h"

//#define DEBUG

#ifdef DEBUG
#include <iostream>
#endif


/*******************************************************************\

Function: refine

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool nodet::refine(
  const namespacet &ns,
  merge_full_irept &merge,
  const exprt &other)
{  
  if(label.is_nil())
    label=other;
  else
  {    
    exprt old_label=label;
 
    impara_conjoin(other, label, ns);    
    simplify(label,ns);   
    
    merge(label);
    
    if(old_label==label)
    	return false;
    
    uncover_all();
  }
  
  if(label.is_false())
    ++coverings;
  
  return true;
}

/*******************************************************************\

Function: add_cover

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

unsigned node_reft::add_cover(node_reft node_ref) 
{
  get().cover.push_back(node_ref);

  nodet &other=*node_ref;
  
  ++other.coverings;

  return other.uncover_all();
} 

/*******************************************************************\

Function: is_covered

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool nodet::is_covered() const 
{
  if(coverings > 0)
    return true;

  for(node_reft current=predecessor;
      !current.is_nil();
      --current) 
  {
    if(current->coverings > 0) 
      return true;
  }
  
  return false;
}



/*******************************************************************\

Function: node_reft::ancestors_same_class

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void node_reft::ancestors_same_class(std::vector<node_reft> &result)
{
  for(node_reft current=get().predecessor;
      !current.is_nil();
      --current) 
  {
    if(current.node_equiv_class==node_equiv_class) 
      result.push_back(current);
  }
}

/*******************************************************************\

Function: nearest_common_ancestor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

node_reft node_reft::nearest_common_ancestor(const node_reft other) const
{
  node_reft current1 = *this;
  node_reft current2 = other;

  while(true) 
  {
    if(current1.is_nil() || current2.is_nil())
      break;
      
    const nodet &node1=*current1;
    const unsigned number1=node1.number;
    const nodet &node2=*current2;
    const unsigned number2=node2.number;

    if(number1==number2 && node1.has_label())
      break;
 
    if(number1 > number2) 
      --current1;
    else
      --current2;
  }

  return current1;
}

/*******************************************************************\

Function: uncover_all

  Inputs:

 Outputs: number of nodes uncovered

 Purpose:

\*******************************************************************/


unsigned nodet::uncover_all() 
{
  for(node_reft::listt::iterator 
      it =cover.begin(); 
      it!=cover.end(); 
      ++it) 
  {
    nodet &node = **it;
    --node.coverings;
  }
	
	unsigned result=cover.size();

  cover.clear();
  
  return result;
}

/*******************************************************************\

Function: has_label

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/


bool nodet::has_label() const
{
  return label.is_not_nil();
}


/*******************************************************************\

Function: node_equiv_classt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

node_equiv_classt::node_equiv_classt(const locst &locs, const global_vectort& global_vector)
{
}
