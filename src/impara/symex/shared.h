/*******************************************************************\

Module: Computing shared accesses.

Author: Bjorn Wachter, bjoern.wachter@gmail.com

\*******************************************************************/

#ifndef CPROVER_SYMEX_SHARED_H
#define CPROVER_SYMEX_SHARED_H

#include "state.h"

class sharedt
{
public:

  typedef std::set<unsigned> sett;

  sharedt(statet& _state)
  : state(_state)
  {}

  void operator()(sett& reads, sett& writes);

protected:
  statet& state;

  void operator()(
    const goto_programt::instructiont& instruction,
    sett &reads, sett &writes);

  bool shared(const exprt& expr, sett& vars);
  bool shared_rec(const exprt& expr, sett& vars);
};

#endif
