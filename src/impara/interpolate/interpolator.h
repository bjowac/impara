/*******************************************************************\

Module: Interpolation

Author: Daniel Kroening, kroening@kroening.com
        Bjorn Wachter, bjoern.wachter@gmail.com

\*******************************************************************/

#ifndef CPROVER_IMPARA_INTERPOLATOR_H
#define CPROVER_IMPARA_INTERPOLATOR_H

#include <util/options.h>
#include <path-symex/locs.h>

#include <nodes.h>

struct cmp_node_reft
{
  inline unsigned operator()(const node_reft &n1,
                             const node_reft &n2) const 
  { return n1->number < n2->number; }
};

//
// generic interpolator class
//
class interpolatort
{
public:
  typedef std::map<node_reft, exprt, cmp_node_reft> interpolant_mapt;

  interpolatort(
    const namespacet& _ns,
    const optionst& _options):
    ns(_ns),
    options(_options)
  {
  }

  virtual decision_proceduret::resultt operator()(
    impara_step_reft history,
    node_reft node_ref,
    node_reft ancestor,
    const exprt& start,
    const exprt& cond,
    interpolant_mapt&)=0;

protected:
  const namespacet &ns;
  const optionst &options;
};

//
// weakest-precondition-based interpolator
//
class wp_interpolatort : interpolatort
{
public:

  wp_interpolatort(
    const namespacet& _ns,    
    const optionst& _options):
    interpolatort(_ns,_options)
  {
  }


  virtual decision_proceduret::resultt operator()(
    impara_step_reft history,
    node_reft node_ref,
    node_reft ancestor,
    const exprt& start,
    const exprt& cond,
    interpolant_mapt&);
};

//
// interpolation by conversion into supported theory
//
class conv_interpolatort : interpolatort
{
public:

  conv_interpolatort(
    const namespacet& _ns,
    const optionst& _options):
    interpolatort(_ns,_options)
  {
  }


  virtual decision_proceduret::resultt operator()(
    statet& state, 
    node_reft ancestor,
    const exprt& start,
    const exprt& cond,
    interpolant_mapt&);
};

#endif
