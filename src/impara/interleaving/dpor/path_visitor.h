/*******************************************************************\

Module: 

Author: Bjorn Wachter

\*******************************************************************/

#ifndef CPROVER_IMPARA_PATH_VISITOR_H
#define CPROVER_IMPARA_PATH_VISITOR_H

#include <vector>

#include <symex/impara_history.h>

#include "happens_before.h"

class path_visitort {
  public:

  typedef std::vector<impara_step_reft> patht;

  virtual void operator()(patht &path, node_reft terminal) 
  { 
    // ... 
  }
};

class dpor_path_visitort : public path_visitort
{
public:

  typedef std::map<node_reft, thread_sett >  backtrackt;

  dpor_path_visitort(
    locst &__locs,
    impara_var_mapt &__var_map,
    backtrackt &__backtrack,
    bool __only_pointers)
  : locs(__locs),
    var_map(__var_map),
    backtrack(__backtrack),
    only_pointers(__only_pointers)
  {}

  virtual void operator()(patht &__path, 
                          node_reft terminal)
  {
    path=__path;

    std::reverse(path.begin(), path.end());

    happens_before(locs, var_map, path, terminal, backtrack, only_pointers);
  }

protected:
  locst &locs;
  impara_var_mapt &var_map;
  node_reft terminal;
  backtrackt &backtrack; 
  patht path; //typedef vector<impara_step_reft> patht
  bool property_sensitive;
  bool only_pointers;
};

void forall_prefixes(
    node_reft terminal,
    path_visitort &visitor);

void forall_prefixes_through(
    node_reft terminal,
    path_visitort &visitor,
    node_reft through
    );


#endif
