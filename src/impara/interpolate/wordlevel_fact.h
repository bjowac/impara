/*******************************************************************\

Module: Facts stored by the wordlevel interpolator

Author: Georg Weissenbacher, georg@weissenbacher.name

\*******************************************************************/

#ifndef CPROVER_WORDLEVEL_FACT_H
#define CPROVER_WORDLEVEL_FACT_H

#include "wordlevel_interpolator.h"

class wordlevel_factt
{
public:
  typedef enum { TOPLEVEL_FACT, 
                 THEORY_FACT, // variable free axiom of the theory, e.g. 1<2
                 INEQUALITY_INTERPOLATOR, 
                 DISEQUALITY_INTERPOLATOR,
                 UIF_INTERPOLATOR,
                 CONSTANT_PROPAGATION,
                 DYNAMIC_OBJECT_POOL,
                 ARRAY_INTERPOLATOR,
                 ARITHMETIC_INTERPOLATOR,
                 TRANSITIVITY_INTERPOLATOR } derivationt;

  typedef unsigned partitiont;

  const exprt expression;
  const partitiont partition;
  const derivationt derivation;

  wordlevel_factt(const exprt& _expression, 
                  const partitiont _partition=0,
                  const derivationt _derivation=wordlevel_factt::TOPLEVEL_FACT):
    expression(_expression), partition(_partition), derivation(_derivation) { }

  wordlevel_factt(const wordlevel_factt& fact):
    expression(fact.expression), partition(fact.partition),
    derivation(fact.derivation) { }
};

typedef std::list<wordlevel_factt> wordlevel_factst;

class graph_factt
{
public:
  typedef enum { EQUAL=0x01, 
                 GREATER_THAN=0x02, 
                 GREATER_EQUAL_THAN=0x04, 
                 NOT_EQUAL=0x08,
                 UNKNOWN=0x10 } relationt;
  
  wordlevel_factt::derivationt derivation;
  wordlevel_factt::partitiont partition;
  unsigned n, m;
  relationt rel;

  bool operator<(const graph_factt&) const;
  bool operator==(const graph_factt&) const;

  typedef struct 
  {
    size_t operator()(const graph_factt& f) const
    {
      return (size_t)(f.n ^ (f.m << 12) ^ 
                      (f.derivation << 24) ^ (f.rel << 28));
    }
  } graph_fact_hasht;

  static graph_factt::relationt merge_relations
  (graph_factt::relationt, graph_factt::relationt);

  static irep_idt relation_to_string(graph_factt::relationt rel)
  {
    switch (rel)
    {
    case graph_factt::EQUAL:
      return irep_idt("=");
    case graph_factt::GREATER_THAN:
      return irep_idt(">");
    case graph_factt::GREATER_EQUAL_THAN:
      return irep_idt(">=");
    case graph_factt::NOT_EQUAL:
      return irep_idt("notequal");
    default:
      return irep_idt("?");
    }
  }

  exprt to_expression(const class expression_poolt&) const;
};

typedef std::list<graph_factt> graph_fact_listt;

class graph_interpolantt
{
public:
  graph_interpolantt() { }
  graph_interpolantt(const graph_factt&);

  typedef enum { A_CHAIN, B_CHAIN } chain_typet;

  typedef std::pair<graph_fact_listt, graph_factt> justificationt;
  typedef std::list<justificationt> justification_listt;

  class chaint
  {
  public:
    graph_fact_listt premises; // A-premises, I in the paper
    justification_listt justifications; // justified B-chains, J 

    /* the current premise:              
       An A-premise, if chain type is B   
       A B-premise, if chain type is A    */
    graph_fact_listt current_premise; 

    graph_factt fact;

    chaint(const graph_factt& _fact): fact(_fact) { }
  };

  typedef std::list<chaint> chain_listt;
  chain_listt chains;

  bool merge_chains(graph_interpolantt&, wordlevel_factt::partitiont);
  bool mend_chain(wordlevel_factt::partitiont);

  void lift_chains(const graph_factt&, wordlevel_factt::partitiont);

  exprt to_expression(const chaint&, expression_poolt&);

  static chain_typet chain_type(const chaint&, wordlevel_factt::partitiont);
protected:

  // pretty printing
  exprt to_expression(const graph_fact_listt&, 
                     const class expression_poolt&) const;
  exprt to_expression(const justificationt&, 
                     const class expression_poolt&) const;
};

#endif
