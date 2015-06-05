/*******************************************************************\

Module: Unwound CFG Nodes

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_IMPARA_NODE_UTILS_H
#define CPROVER_IMPARA_NODE_UTILS_H

#include "node.h"

typedef std::vector<loc_reft> local_call_stackt;
typedef std::vector<local_call_stackt > global_vectort;
typedef std::vector<nodet> node_containert;


struct global_vector_equalityt
{
  inline bool operator()(const global_vectort& v1, const global_vectort& v2) const
  {
    if(v1.size() != v2.size())
      return false;

    for(unsigned thr=0;thr<v1.size();++thr)
    {
      const local_call_stackt& lcs1=v1[thr];
      const local_call_stackt& lcs2=v2[thr];

      if(lcs1.size() != lcs2.size())
      	return false;
      for(int i=lcs1.size()-1; i>=0; --i)
      {
      	if(lcs1[i]!=lcs2[i]) return false;
      }
    }
    
    return true;
  }
};

struct global_vector_hasht
{
  static const int N = 2147483647;

  inline int operator()(const global_vectort& v) const
  {
    static const int w[] = {234, 739, 934, 23, 828, 194};  
    int result = 0;

    for(unsigned thr=0;thr<v.size();++thr)
    {
      const local_call_stackt& lcs=v[thr];

      for (unsigned i = 0; i < lcs.size(); ++i) 
        result = (result + w[i % 6] * lcs[i].loc_number) % N;
    }

    return result;
  }
};

#endif
