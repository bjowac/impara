/*******************************************************************\

Module: Interface for wordlevel interpolators

Author: Georg Weissenbacher, georg@weissenbacher.name

Info:   The interpolator for transitivities consists of
        three components. 
        * The inequality_interpolator deals exclusively with
          ineqalities (>, >=). It infers contradictions
          by constructing a directed graph and searching
          for strongly connected components that include
          >-edges. This components also infers additional
          equalities (from SCCs that contain only >=).
          Theory-specific inequality chains for constants
          (e.g., 17>12>3) are added on demand.
          * The disequality_interpolator deals exclusively with
          equalities and disequalities (==, !=). It uses
          a union-find data-structure to search for contradictions.
          Theory-specific inequalities (e.g. 'a'!='b')
          are added on demand.
          * The expression pool assigns unique IDs to expressions
          and keeps track of the constants used in the formula.
          It is used by the other components to derive theory
          specific facts (inequality chains, disequalities).
          * The UIF interpolator deals with uninterpreted functions.
          * The constant propagator propagates constants and 
          simplifies the resulting expressions

\*******************************************************************/

#ifndef CPROVER_WORDLEVEL_INTERPOLATOR_H
#define CPROVER_WORDLEVEL_INTERPOLATOR_H

#include <vector>
#include <map>
#include <set>

#include <util/std_expr.h>
#include <util/type.h>
#include <util/graph.h>
#include <util/numbering.h>
#include <util/hash_cont.h>

// for pretty printing
#include <util/namespace.h>
#include <langapi/language_util.h>
#include <util/decision_procedure.h>

#include "wordlevel_fact.h"

typedef graph_nodet<> empty_nodet;

/*******************************************************************\

 General interfaces

\*******************************************************************/

class wordlevel_interpolatort
{
public:
  virtual void add_formulas(const expr_listt&,
                            wordlevel_factt::partitiont partition=0)=0;
  virtual void add_formula(const exprt&, wordlevel_factt::partitiont)=0;
  virtual void set_maximal_partition(wordlevel_factt::partitiont)=0;
  virtual decision_proceduret::resultt infer()=0;
  virtual void get_interpolant(wordlevel_factt::partitiont, exprt&)=0;
  virtual void get_interpolants(expr_listt&)=0;
  virtual ~wordlevel_interpolatort () { }

protected:
  virtual void add_fact(const wordlevel_factt&)=0;
};

class graph_interpolator_callbackt
{
public:
  virtual bool add_fact(const graph_factt&)=0;
  virtual void report_contradiction(const graph_factt&)=0;
  virtual bool get_interpolant(const graph_factt&,
                               wordlevel_factt::partitiont,
                               graph_interpolantt&)=0;
  virtual ~graph_interpolator_callbackt () { }
};

/*******************************************************************\

   Class: justificationst

 Purpose: A class used to store facts, the corresponding 
          original facts, and their respective justifications.

\*******************************************************************/
class justificationst 
{
public:
  justificationst()
  {
  }

  // types to store justifications
  typedef std::vector<graph_fact_listt> justificationt;

  typedef hash_map_cont<graph_factt, justificationt, 
                        graph_factt::graph_fact_hasht> justification_mapt;

  typedef hash_map_cont<graph_factt, graph_factt, 
                        graph_factt::graph_fact_hasht> original_fact_mapt;
  
  void add_justification(const graph_factt&, justificationt&);
  void add_justification(const graph_factt&, graph_fact_listt&);
  bool has_justification(const graph_factt&);
  const justificationt& get_justification(const graph_factt&);

  void add_original_fact(const graph_factt&, const graph_factt&);
  graph_factt get_original_fact(const graph_factt&);

protected:
  justification_mapt justification_map;
  original_fact_mapt original_facts;
};

/*******************************************************************\

   Class: graph_based_interpolatort

 Purpose: Defines basic functionality of a graph-based interpolator

\*******************************************************************/
class graph_based_interpolatort
{
public:
  typedef std::list<unsigned> patht;

  graph_based_interpolatort(): inconsistent(false) { };
  virtual wordlevel_factt::derivationt derivation_type()=0;
  virtual bool add_fact(const graph_factt&)=0;
  virtual void fact_from_edge(unsigned, unsigned, graph_factt&)=0;
  virtual bool infer(graph_interpolator_callbackt&)=0;
  virtual bool get_interpolant(const graph_factt&,
                               wordlevel_factt::partitiont,
                               graph_interpolator_callbackt&,
                               graph_interpolantt&);
  virtual ~graph_based_interpolatort () { }

protected:
  bool inconsistent; // to store the contradicting fact
  graph_factt contradiction;
  
  // data structure for caching chains 
  typedef std::map<const graph_factt, patht, 
                   std::less<const graph_factt> > path_cachet;

  path_cachet path_cache;

  justificationst justifications;
  
  virtual void remember_justification(const graph_factt&);
  virtual bool get_actual_fact(const graph_factt&, graph_factt&)=0;
  virtual void find_chains(const graph_fact_listt& facts, 
                           wordlevel_factt::partitiont threshold, 
                           graph_interpolator_callbackt& callback,
                           graph_interpolantt& interpolant);
  virtual void find_chains(const patht& path, 
                           wordlevel_factt::partitiont threshold, 
                           graph_interpolator_callbackt& callback,
                           graph_interpolantt& interpolant);
  virtual patht& trace_fact(const graph_factt&)=0;
};

/*******************************************************************\

 Expression pool

\*******************************************************************/

typedef std::pair<wordlevel_factt::partitiont, 
                  wordlevel_factt::partitiont> colour_ranget;

class expression_poolt
{
public:
  expression_poolt(const namespacet&);
  unsigned number(const exprt&);
  unsigned number(const exprt&, wordlevel_factt::partitiont colour);
  unsigned number(const exprt&, const colour_ranget &range);

  const exprt& operator[](unsigned) const;
  unsigned size() const;

  bool is_constant(unsigned n) const 
  { return expression_numbers[n].is_constant(); }

  bool is_numeric(unsigned n) const
  { return is_number(expression_numbers[n].type()); }

  bool get_number(const exprt& expression, unsigned &n) const
  { return expression_numbers.get_number(expression, n); }

  decision_proceduret::resultt compare_constants(unsigned, unsigned);

  bool get_colour(unsigned n, colour_ranget &range) const;
  void set_colour (unsigned n, wordlevel_factt::partitiont colour);
  void add_colour (unsigned n, wordlevel_factt::partitiont colour);
  void add_colour (unsigned n, const colour_ranget &range);
  void inherit_colour (unsigned n, unsigned m);
  bool is_colourable(unsigned n, wordlevel_factt::partitiont colour) const;

  std::string to_string(unsigned);

  unsigned number_true() const { return true_num; }
  unsigned number_false() const { return false_num; }

  const namespacet &ns;

protected:
  hash_numbering<exprt, irep_hash> expression_numbers;
  std::vector<colour_ranget> colouring;

  unsigned true_num;
  unsigned false_num;
  unsigned max_partition;

  void massage(exprt& expression);
};

/*******************************************************************\

 A rewriter, instantiating a set of very simple rewriting rules
 on demand, e.g., 
   t0 = (t1+1)  |->  t1 != (t1+1), 
   t0 = (t1<<1) |->  (t1<<1) = t1+t1 (or 2*t1)

\*******************************************************************/

#include "wordlevel_axioms.h"

class graph_axiomst
{
public:
  graph_axiomst(expression_poolt&);

  void add_fact(const graph_factt&);
  void infer(graph_interpolator_callbackt&);

  void add_axiom(const graph_factt&, unsigned);
protected:
  expression_poolt &expression_pool;
  std::vector<bool> processed;

  GRAPH_RULE_DECLARATIONS;

  typedef std::list<std::pair<graph_factt, unsigned> > axiom_poolt;

  axiom_poolt axiom_pool; // inferred axioms

  void rewrite_term(unsigned, wordlevel_factt::partitiont);
  void rewrite_fact(const graph_factt&);
};


/*******************************************************************\

 Inequality interpolator (>, >=)

\*******************************************************************/

class inequality_edget: public empty_nodet
{
public:
  graph_factt::relationt rel;
  wordlevel_factt::derivationt derivation;
  wordlevel_factt::partitiont partition;
};

class inequality_grapht: public graph<graph_nodet<inequality_edget> >
{
};

/*******************************************************************\

   Class: inequality_interpolatort

 Purpose: Interpolation for >= and >

\*******************************************************************/

class inequality_interpolatort: public graph_based_interpolatort
{
public:
  bool add_fact(const graph_factt& f);
  void fact_from_edge(unsigned, unsigned, graph_factt&);
  bool infer(graph_interpolator_callbackt& c);
  wordlevel_factt::derivationt derivation_type() { return wordlevel_factt::INEQUALITY_INTERPOLATOR; }

protected:
  inequality_grapht inequality_graph;

  patht& trace_fact(const graph_factt& fact);
  bool get_actual_fact(const graph_factt&, graph_factt& actual_fact);
};


/*******************************************************************\

 Disequality interpolator (==, !=)

\*******************************************************************/

class disequality_edget: public empty_nodet
{
public:
  wordlevel_factt::derivationt derivation;
  wordlevel_factt::partitiont partition;
  unsigned indirection; // to store edges from which fact is derived
};

/*******************************************************************\

   Class: disequality_grapht

 Purpose: union find implementation for (dis)equalities

\*******************************************************************/

class disequality_grapht: public graph<graph_nodet<disequality_edget> >
{
public:
  void make_set(unsigned node);
  unsigned make_union(const graph_factt& fact);
  unsigned find(unsigned current);
  bool same_set(unsigned a, unsigned b) { return find(a)==find(b); }

  bool add_indirect_edge(unsigned, unsigned, unsigned, 
                         wordlevel_factt::derivationt);
  
  // the constructor takes a reference to the expression pool
  // and a stack that will be used to store inferred inequalities
  disequality_grapht(const expression_poolt &pool): 
    expression_pool(pool) { }

  void trace_fact(unsigned n, unsigned m, patht& path);

  class union_callbackt {
  public:
    virtual void add_class(unsigned)=0;
    virtual void merge(unsigned, unsigned)=0;
    virtual ~union_callbackt() { }
  };
    
  void register_callback(union_callbackt*);

protected:
  // shared with superordinate interpolator, and read-only:
  const expression_poolt &expression_pool;

  std::list<union_callbackt *> callbacks;

  struct vertext
  {
    unsigned rank;
    unsigned parent;
    bool root;

    vertext(): rank(1), root(true) { }
  };
  std::vector<vertext> vertices;

  void triangulate(unsigned, unsigned, unsigned, unsigned);
  void merge_constant_info(unsigned n, unsigned m);
  
  void run_add_callbacks(unsigned);
  void run_merge_callbacks(unsigned, unsigned);
};

/*******************************************************************\

   Class: disequality_interpolatort

 Purpose: Interpolation for = and !=

\*******************************************************************/

class disequality_interpolatort: public graph_based_interpolatort
{
public:
  disequality_interpolatort(expression_poolt &pool): 
    expression_pool(pool), 
    union_find(expression_pool)
  { 
  }

  bool add_fact(const graph_factt&);
  void fact_from_edge(unsigned, unsigned, graph_factt&);
  bool infer(graph_interpolator_callbackt&);
  wordlevel_factt::derivationt derivation_type() { return wordlevel_factt::DISEQUALITY_INTERPOLATOR; }

  // functions used by uif_interpolatort
  unsigned get_representative(unsigned n)
  { return union_find.find(n); }

  void register_callback(disequality_grapht::union_callbackt* c)
  { union_find.register_callback(c); }

protected:
  // following classes need access to tracefact and find_chains
  friend class congruencest;
  friend class constant_propagationt;
  friend class uif_interpolatort;
  friend class array_propagationt;
  friend class dynamic_object_poolt;
  friend class arithmetic_interpolatort;
  
  expression_poolt &expression_pool;
  disequality_grapht union_find;
  std::set<graph_factt> inequality_facts;

  bool get_actual_fact(const graph_factt&, graph_factt& actual_fact);
  patht& trace_fact(const graph_factt& fact);
};

/*******************************************************************\

   Class: congruencest

 Purpose: A class used to store congruence edges and their
          respective justifications. This is used by the
          uif_interpolatort and by constant_propagationt

\*******************************************************************/
class congruencest 
{
public:
  congruencest(
    expression_poolt &pool,
    disequality_interpolatort &di):
    expression_pool(pool),
    disequality_interpolator(di)
  {
  }

  // congruence edges for an equality
  typedef std::vector<graph_based_interpolatort::patht> pathst;
  typedef std::pair<unsigned, unsigned> congruencet;

  struct congruence_hasht
  {
    size_t operator()(const congruencet& c) const
    {
      return (size_t)(c.first ^ (c.second << 16));
    }
  };
  
  typedef hash_map_cont<congruencet, pathst, congruence_hasht> congruence_mapt;
  
  void add_fact(const graph_factt &fact);
  void add_fact(const graph_factt &fact, unsigned, unsigned);
  const pathst& get_justification(const graph_factt&);

protected:
  expression_poolt &expression_pool;
  disequality_interpolatort &disequality_interpolator;
  
  congruence_mapt congruence_map;
};

/*******************************************************************\

   Class: uif_interpolatort

 Purpose: Interpolation for uninterpreted functions.
          This class implements the congruence closure
          algorithm presented by Nieuwenhuis and Oliveras in
          "Proof-producing Congruence Closure" 

\*******************************************************************/

class uif_interpolatort: public disequality_grapht::union_callbackt
{
public:
  uif_interpolatort(
    expression_poolt &pool,
    disequality_interpolatort &di): 
    expression_pool(pool),
    disequality_interpolator(di),
    congruences(expression_pool, disequality_interpolator)
  { 
    disequality_interpolator.register_callback(this);
  }

  bool infer(graph_interpolator_callbackt& callback);

  bool get_interpolant(const graph_factt&,
                       wordlevel_factt::partitiont,
                       graph_interpolator_callbackt&,
                       graph_interpolantt&);

  // the callback function for the disequality interpolator
  void add_class(unsigned);
  void merge(unsigned, unsigned);

protected:
  expression_poolt &expression_pool;
  std::vector<bool> processed;

  disequality_interpolatort &disequality_interpolator;

  congruencest congruences;

  graph_fact_listt pending;

  // members for Nieuwenhuis/Oliveras' proof-producing congruence closure
  typedef hash_map_cont<unsigned, unsigned> lookup_tablet;
  typedef hash_map_cont<unsigned, std::list<unsigned> > use_listt;

  lookup_tablet lookup_table;
  use_listt use_list;

  bool lookup(unsigned n, unsigned &result);

  void colour_fact(const graph_factt&, 
                   wordlevel_factt::partitiont,
                   std::list<graph_factt>&,
                   std::list<graph_interpolantt>&);
};


/*******************************************************************\

   Class: constant_propagationt

 Purpose: Interpolation for interpreted constants and 
          simplifications.

\*******************************************************************/

class constant_propagationt: public disequality_grapht::union_callbackt
{
public:
  constant_propagationt(
    expression_poolt &pool,
    disequality_interpolatort &di): 
    expression_pool(pool),
    disequality_interpolator(di),
    congruences(expression_pool, disequality_interpolator)
  { 
    disequality_interpolator.register_callback(this);
  }

  bool infer(graph_interpolator_callbackt& callback);

  bool get_interpolant(const graph_factt&,
                       wordlevel_factt::partitiont,
                       graph_interpolator_callbackt&,
                       graph_interpolantt&);

  bool get_constant_info(unsigned n, unsigned &c);

  // the callback function for the disequality interpolator
  void add_class(unsigned);
  void merge(unsigned, unsigned);

  // function to notify the propagator about new facts
  bool add_fact(const graph_factt&);

protected:
  expression_poolt &expression_pool;
  disequality_interpolatort &disequality_interpolator;

  congruencest congruences;
  
  struct constant_infot
  {
    bool has_representative_constant;
    unsigned representative_constant;

    constant_infot(): has_representative_constant(false) { }
  };
  std::vector<constant_infot> representative_constants;
  std::stack<graph_factt> inferred_disequalities;

  struct ordert
  {
    bool operator()(const constant_exprt&, const constant_exprt&) const;
  };

  // separate chains of constants for fixedbv, floatbv, etc.
  typedef std::map<constant_exprt, unsigned, ordert> typed_constant_poolt;
  typedef hash_map_cont<typet, typed_constant_poolt, irep_hash> constant_poolt;

  constant_poolt constant_pool;

  std::set<unsigned> term_pool;

  // the function to add constants to inequality chains
  bool add_constant(const exprt &expr, unsigned number);
  void add_subterms(unsigned);

  void infer_inequalities(graph_interpolator_callbackt& callback);
  void infer_disequalities(graph_interpolator_callbackt& callback);

  bool simplify_to_constant(exprt&);
  bool simplify_typecast_to_constant(exprt&);
};

/*******************************************************************\

   Class: array_propagationt

 Purpose: Interpolation for arrays.
          This class adds array and field equalities on
          demand.

\*******************************************************************/

class array_propagationt
{
public:
  array_propagationt(
    expression_poolt &pool,
    disequality_interpolatort &di,
    constant_propagationt &cp): 
    expression_pool(pool),
    disequality_interpolator(di),
    constant_propagation(cp),
    congruences(expression_pool, disequality_interpolator)
  { 
  }

  void add_fact(const graph_factt&);
  bool infer(graph_interpolator_callbackt& callback);

  bool get_interpolant(const graph_factt&,
                       wordlevel_factt::partitiont,
                       graph_interpolator_callbackt&,
                       graph_interpolantt&);
 
protected:
  expression_poolt &expression_pool;
  disequality_interpolatort &disequality_interpolator;
  constant_propagationt &constant_propagation;

  congruencest congruences;

  struct array_updatet
  {
    exprt with;
    graph_factt fact;
  };

  typedef hash_map_cont<exprt, array_updatet, irep_hash> array_updatest;
  typedef std::multimap<unsigned, unsigned> array_accessest;

  array_updatest array_updates;
  array_accessest array_accesses;

  void add_subterms(const exprt&, wordlevel_factt::partitiont);
};

/*******************************************************************\

   Class: dynamic_object_poolt

 Purpose: Tracking of non-null objects.
          This class adds ptr != NULL if we can infer that
          ptr points to a valid object.

\*******************************************************************/

class dynamic_object_poolt:
  public disequality_grapht::union_callbackt
{
public:
  dynamic_object_poolt(
    expression_poolt &pool,
    disequality_interpolatort &di):
    expression_pool(pool),
    disequality_interpolator(di),
    congruences(expression_pool, disequality_interpolator)
  { 
    disequality_interpolator.register_callback(this);
  }

  bool infer(graph_interpolator_callbackt& callback);

  bool get_interpolant(const graph_factt&,
                       wordlevel_factt::partitiont,
                       graph_interpolator_callbackt&,
                       graph_interpolantt&);

  // the callback function for the disequality interpolator
  void add_class(unsigned);
  void merge(unsigned, unsigned);
 
protected:
  expression_poolt &expression_pool;
  disequality_interpolatort &disequality_interpolator;

  congruencest congruences;

  typedef hash_map_cont<unsigned, unsigned> valid_objectst;
  valid_objectst valid_objects;

  typedef hash_map_cont<typet, std::set<unsigned>, irep_hash> object_poolt;
  object_poolt object_pool;

  typedef hash_map_cont<unsigned, std::list<unsigned> > use_listt;
  use_listt use_list;

  graph_fact_listt pending;

  void process_subterms(unsigned, const exprt&);
  bool is_valid_object(const exprt&);
  void add_to_object_pool(unsigned, const exprt&);
  void process_uselist(unsigned);
  void add_justification(unsigned, unsigned, unsigned, unsigned);
};

/*******************************************************************\

   Class: arithmetic_interpolatort

 Purpose: Very simple arithmetic rules such as
          n < 0 |- false
          n < 1 |- n=0
          (where n is of type unsigned)

\*******************************************************************/

class arithmetic_interpolatort
{
public:
  arithmetic_interpolatort(
    expression_poolt &pool,
    disequality_interpolatort &di,
    constant_propagationt &cp):
    inconsistent(false),
    expression_pool(pool),
    disequality_interpolator(di),
    constant_propagation(cp),
    congruences(expression_pool, disequality_interpolator)
  {
  }

  void add_fact(const graph_factt&);
  bool infer(graph_interpolator_callbackt&);

  bool get_interpolant(const graph_factt&,
                       wordlevel_factt::partitiont,
                       graph_interpolator_callbackt&,
                       graph_interpolantt&);

protected:
  bool inconsistent; // to store the contradicting fact
  graph_factt contradiction;

  expression_poolt &expression_pool;
  disequality_interpolatort &disequality_interpolator;
  constant_propagationt &constant_propagation;

  congruencest congruences;

  typedef std::map<graph_factt, graph_factt> premisest;
  premisest premises;

  typedef hash_map_cont<unsigned, 
                        graph_fact_listt> postponed_factst;
  postponed_factst postponed_facts;

  typedef enum { INEQUALITY_DERIVATION,
                 EQUALITY_DERIVATION } derivation_typet;
  typedef std::map<graph_factt, derivation_typet> derivation_typest;
  derivation_typest derivation_types;

  void process_greater_than(const graph_factt& fact,
                            graph_interpolator_callbackt&);
};


/*******************************************************************\

   Class: transitivity_interpolatort

 Purpose: Transitivity interpolator (>, >=, ==, !=)
          Also knows theory axioms (e.g., 2>1, 'a'!='b')

\*******************************************************************/

class transitivity_interpolatort: public wordlevel_interpolatort, 
                                  public graph_interpolator_callbackt
{
public:
  transitivity_interpolatort(const namespacet&);
  void add_formulas(const expr_listt&, wordlevel_factt::partitiont);
  void add_formula(const exprt&, wordlevel_factt::partitiont);
  decision_proceduret::resultt infer();
  void get_interpolant(wordlevel_factt::partitiont, exprt&);
  void get_interpolants(expr_listt&);

  /* callback functions */
  bool add_fact(const graph_factt& f);
  void report_contradiction(const graph_factt& f);
  bool get_interpolant(const graph_factt&,
                       wordlevel_factt::partitiont,
                       graph_interpolantt&);

  /* set the highest partition number in the formula */
  void set_maximal_partition(wordlevel_factt::partitiont partition)
  { maximal_partition=partition; }

  virtual ~transitivity_interpolatort () { }

protected:
  const namespacet &ns;

  /* interpolators used by transitivity_interpolator */
  expression_poolt expression_pool;
  graph_axiomst graph_axioms;  
  inequality_interpolatort inequality_interpolator;
  disequality_interpolatort disequality_interpolator;
  uif_interpolatort uif_interpolator;
  constant_propagationt constant_propagation;
  dynamic_object_poolt dynamic_object_pool;
  array_propagationt array_propagation;
  arithmetic_interpolatort arithmetic_interpolator;

  graph_factt contradiction; // to store the contradicting fact
  bool inconsistent;
  bool facts_changed; // updated by add_fact callback
  
  wordlevel_factt::partitiont maximal_partition;

  void add_fact(const wordlevel_factt& f);
  bool canonicalise(const exprt& expression, graph_factt& fact);

  void check_for_constants(const graph_factt& fact);
};

#endif
