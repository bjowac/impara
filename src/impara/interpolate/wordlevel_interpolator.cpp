
/*******************************************************************\

Module: Wordlevel interpolation

Author: Georg Weissenbacher, georg@weissenbacher.name

\*******************************************************************/

#include <util/type.h>

#include <util/std_expr.h>
#include <util/simplify_expr.h>
#include <util/simplify_expr_class.h>
#include <util/arith_tools.h>
#include <util/mp_arith.h>
#include <util/fixedbv.h>
#include <util/ieee_float.h>
#include <util/rational.h>
#include <util/rational_tools.h>

#include "wordlevel_interpolator.h"
#include "wordlevel_axioms.h"

//#define DEBUG

/*******************************************************************\

Function: transitivity_interpolatort::transitivity_interpolatort

  Inputs: 

 Outputs: 

 Purpose: Constructor for the transitivity interpolator

\*******************************************************************/
transitivity_interpolatort::transitivity_interpolatort
(const namespacet &_ns): 
  ns(_ns), expression_pool(ns),
  graph_axioms(expression_pool),
  disequality_interpolator(expression_pool),
  uif_interpolator(expression_pool, disequality_interpolator),
  constant_propagation(expression_pool, disequality_interpolator),
  dynamic_object_pool(expression_pool, disequality_interpolator),
  array_propagation(expression_pool, 
                    disequality_interpolator,
                    constant_propagation),
  arithmetic_interpolator(expression_pool, 
                          disequality_interpolator,
                          constant_propagation),
  inconsistent(false), facts_changed(false), maximal_partition(0)
{
}

/*******************************************************************\

Function: swap_nodes

  Inputs: 

 Outputs: 

 Purpose: Swaps the node ids of a graph fact

\*******************************************************************/
static inline void swap_nodes(graph_factt &fact)
{
  unsigned tmp;
  tmp=fact.n; fact.n=fact.m; fact.m=tmp;
}

/*******************************************************************\

Function: transitivity_interpolatort::canonicalise

  Inputs: An expression representing a relation (ideally simplified). 

 Outputs: A canonicalised fact corresponding to the input.
          Returns true if the fact cannot be canonicalised.

 Purpose: Preprocessing for the graph based decision procedures

\*******************************************************************/
bool transitivity_interpolatort::canonicalise(const exprt& expression, 
                                              graph_factt &fact)
{
  if (expression.type().id()!=ID_bool || expression.is_true())
    return true;

  if (expression.id()==ID_not)
  {
    assert(expression.has_operands() && expression.operands().size()==1);
    exprt e=expression.op0();

    if (e.id()==ID_not && e.type().id()==ID_bool)
    {
      assert(e.has_operands() && e.operands().size()==1);
      return canonicalise(e.op0(), fact);
    }
    
    if(e.is_false())
      return true;

    if(e.is_true())
    {
      fact.n=expression_pool.number_false();
      fact.m=fact.n;
      fact.rel=graph_factt::NOT_EQUAL;
      return false;
    }
      
    if (e.id()==ID_symbol || 
        expression.id()==ID_extractbits || 
        (e.has_operands() && e.operands().size()!=2))
    {
      fact.n=expression_pool.number(e, fact.partition);
      fact.m=expression_pool.number_true();
      fact.rel=graph_factt::NOT_EQUAL;
      return false;
    }

    assert(e.operands().size()==2);

    if (e.op0()==e.op1() && (e.id()=="<" || e.id()==">"))
      return true; // this is useless!!

    fact.n=expression_pool.number(e.op0(), fact.partition);
    fact.m=expression_pool.number(e.op1(), fact.partition);

    if (e.id()=="=")
      fact.rel=graph_factt::NOT_EQUAL;
    else if (e.id()=="notequal"||e.id()=="!=")
      fact.rel=graph_factt::EQUAL;
    else if (e.id()=="<")
      fact.rel=graph_factt::GREATER_EQUAL_THAN;
    else if (e.id()==">")
    {
      swap_nodes(fact); fact.rel=graph_factt::GREATER_EQUAL_THAN;
    }
    else if (e.id()=="<=")
      fact.rel=graph_factt::GREATER_THAN;
    else if (e.id()==">=")
    {
      swap_nodes(fact); fact.rel=graph_factt::GREATER_THAN;
    }
    else
    {
      // make a disequality out of an otherwise useless fact
      fact.n=expression_pool.number(e, fact.partition);
      fact.m=expression_pool.number_true();
      fact.rel=graph_factt::NOT_EQUAL;
    }
    return false; // success
  }

  if (expression.id()==ID_symbol || 
      expression.id()==ID_extractbits ||
      expression.operands().size()!=2) 
  {
    fact.n=expression_pool.number(expression, fact.partition);
    fact.m=expression_pool.number_true();
    fact.rel=graph_factt::EQUAL;
    return false;
  }

  if(expression.is_false())
  {
    fact.n=expression_pool.number_false();
    fact.m=fact.n;
    fact.rel=graph_factt::NOT_EQUAL;
    return false;
  }
  
  if ((expression.op0()==expression.op1()) &&
       (expression.id()=="=" || expression.id()==">=" 
        || expression.id()=="<="))
    return true; // useless tautology

  
  fact.n=expression_pool.number(expression.op0(), fact.partition);
  fact.m=expression_pool.number(expression.op1(), fact.partition);
  
  if (expression.id()=="=")
    fact.rel=graph_factt::EQUAL;
  else if (expression.id()=="notequal"||expression.id()=="!=")
    fact.rel=graph_factt::NOT_EQUAL;
  else if (expression.id()==">")
    fact.rel=graph_factt::GREATER_THAN;
  else if (expression.id()==">=")
    fact.rel=graph_factt::GREATER_EQUAL_THAN;
  else if (expression.id()=="<")
  {
    swap_nodes(fact); fact.rel=graph_factt::GREATER_THAN;
  }
  else if (expression.id()=="<=")
  {
    swap_nodes(fact); fact.rel=graph_factt::GREATER_EQUAL_THAN;
  }
  else
  {
    // make an equality out of an otherwise useless fact
    fact.n=expression_pool.number(expression, fact.partition);
    fact.m=expression_pool.number_true();
    fact.rel=graph_factt::EQUAL;
  }
  return false; // success
}

/*******************************************************************\

Function: transitivity_interpolatort::add_formula

  Inputs: A list of partitions (conjunctions of facts)

 Outputs: 

 Purpose: Adds the partitions to the fact database and numbers
          them (starting with zero by default).

\*******************************************************************/
void transitivity_interpolatort::add_formulas
(const expr_listt& formulas,
 wordlevel_factt::partitiont partition=0)
{
  for (expr_listt::const_iterator e_it=formulas.begin();
       e_it!=formulas.end(); e_it++, partition++)
    add_formula(*e_it, partition);
}

/*******************************************************************\

Function: transitivity_interpolatort::add_formula

  Inputs: A conjunction wordlevel facts and a partition number

 Outputs: 

 Purpose: Splits a conjunction into subexpressions and adds them
          to the fact database

\*******************************************************************/
void transitivity_interpolatort::add_formula
(const exprt& formula, wordlevel_factt::partitiont partition)
{
  maximal_partition=std::max(maximal_partition, partition);

  if (formula.id()==ID_and)
  {
    forall_operands(f_it, formula)
    {
      add_formula(*f_it, partition);
    }
  }
  else
  {
    wordlevel_factt fact(formula, partition);
    add_fact(fact);
  }
}

/*******************************************************************\

Function: transitivity_interpolatort::add_fact

  Inputs: An wordlevel fact

 Outputs: 

 Purpose: Adds a fact to the wordlevel interpolator fact base

\*******************************************************************/
void transitivity_interpolatort::add_fact(const wordlevel_factt& fact)
{
  graph_factt graph_fact;

  if(inconsistent)
    return; // no more work to be done

  // remember where this comes from
  graph_fact.derivation=fact.derivation; 
  graph_fact.partition=fact.partition;

  if(canonicalise(fact.expression, graph_fact))
    return;

  // run constant propagation and the rewriting rules
  constant_propagation.add_fact(graph_fact);
  graph_axioms.add_fact(graph_fact);

  // process data structure accesses
  array_propagation.add_fact(graph_fact);

  // apply our simple arithmetic rules
  arithmetic_interpolator.add_fact(graph_fact);

  // now hand it over to the appropriate interpolator
  switch(graph_fact.rel)
  {
  case graph_factt::EQUAL:
    disequality_interpolator.add_fact(graph_fact);
    // now split = into >= and <=
    if (expression_pool.is_numeric(graph_fact.n))
    {
      graph_fact.rel=graph_factt::GREATER_EQUAL_THAN;
      inequality_interpolator.add_fact(graph_fact);
      swap_nodes(graph_fact);
      inequality_interpolator.add_fact(graph_fact);
    }
    break;
  case graph_factt::GREATER_THAN:
    if(graph_fact.n==graph_fact.m)
    {
      contradiction=graph_fact;
      inconsistent=true;
    }
    else
      inequality_interpolator.add_fact(graph_fact);
    break;
  case graph_factt::GREATER_EQUAL_THAN:
    inequality_interpolator.add_fact(graph_fact);
    break;
  case graph_factt::NOT_EQUAL:
    if(graph_fact.n==graph_fact.m)
    {
      contradiction=graph_fact;
      inconsistent=true;
    }
    else
      disequality_interpolator.add_fact(graph_fact);
    break;
  case graph_factt::UNKNOWN:
  default:
    assert(false);
  }
}

/*******************************************************************\

Function: transitivity_interpolatort::add_fact

  Inputs: A graph fact

 Outputs: 

 Purpose: Callback function that allows a subordinate
          decision procedure to report new facts. Returns
          true if the fact was already known.

\*******************************************************************/
bool transitivity_interpolatort::add_fact(const graph_factt& fact)
{
  if(inconsistent)
    return true;

  bool known;

  if (fact.rel==graph_factt::EQUAL ||
      fact.rel==graph_factt::NOT_EQUAL)
  {
    known=disequality_interpolator.add_fact(fact);

    if(fact.derivation!=wordlevel_factt::INEQUALITY_INTERPOLATOR &&
       fact.derivation!=wordlevel_factt::ARITHMETIC_INTERPOLATOR &&
       fact.rel==graph_factt::EQUAL &&
       expression_pool.is_numeric(fact.n))
    {
      graph_factt new_fact=fact;
      new_fact.rel=graph_factt::GREATER_EQUAL_THAN;
      known&=inequality_interpolator.add_fact(new_fact);
      swap_nodes(new_fact);
      known&=inequality_interpolator.add_fact(new_fact);
    }
  }
  else 
  {
    assert(fact.rel==graph_factt::GREATER_THAN ||
           fact.rel==graph_factt::GREATER_EQUAL_THAN);
    known=inequality_interpolator.add_fact(fact);
  }
  facts_changed|=!known;

  if(!known) // run the rewriting rules and constant propagation
  {
    constant_propagation.add_fact(fact);
    array_propagation.add_fact(fact);
    graph_axioms.add_fact(fact);
  }
  
  return known;
}

/*******************************************************************\

Function: transitivity_interpolatort::report_contradiction

  Inputs: A graph fact

 Outputs: 

 Purpose: Callback function that allows a subordinate
          decision procedure to report a contradiction

\*******************************************************************/
void transitivity_interpolatort::report_contradiction
(const graph_factt& fact)
{
  assert (fact.rel==graph_factt::GREATER_THAN ||
          fact.rel==graph_factt::NOT_EQUAL);

#ifdef DEBUG
  std::cout << "Contradiction: " << fact.n <<
    (fact.rel==graph_factt::GREATER_THAN?">":"!=") <<
    fact.m << std::endl;
#endif

  contradiction=fact;
  inconsistent=true;
}

/*******************************************************************\

Function: transitivity_interpolatort::get_interpolant

  Inputs: A graph fact, a partition, and an data structure to
          store the result.

 Outputs: 

 Purpose: Callback function that allows a subordinate
          decision procedure get a partial interpolant

\*******************************************************************/
bool transitivity_interpolatort::get_interpolant
(const graph_factt& fact, wordlevel_factt::partitiont partition, 
 graph_interpolantt& interpolant)
{
  switch (fact.derivation)
  {
  case wordlevel_factt::INEQUALITY_INTERPOLATOR:
    return inequality_interpolator.get_interpolant
      (fact, partition, *this, interpolant);
  case wordlevel_factt::DISEQUALITY_INTERPOLATOR:
    return disequality_interpolator.get_interpolant
      (fact, partition, *this, interpolant);
  case wordlevel_factt::UIF_INTERPOLATOR:
    return uif_interpolator.get_interpolant
      (fact, partition, *this, interpolant);
  case wordlevel_factt::CONSTANT_PROPAGATION:
    return constant_propagation.get_interpolant
      (fact, partition, *this, interpolant);
  case wordlevel_factt::DYNAMIC_OBJECT_POOL:
    return dynamic_object_pool.get_interpolant
      (fact, partition, *this, interpolant);
  case wordlevel_factt::ARRAY_INTERPOLATOR:
    return array_propagation.get_interpolant
      (fact, partition, *this, interpolant);
  case wordlevel_factt::ARITHMETIC_INTERPOLATOR:
    return arithmetic_interpolator.get_interpolant
      (fact, partition, *this, interpolant);
  default:
    assert(false);
  }
  return true;
}

/*******************************************************************\

Function: graph_factt::operator<

  Inputs: Two graph_facts

 Outputs: 

 Purpose: Imposes an order between graph_facts. 
          Used for the map that caches chains.

\*******************************************************************/
bool graph_factt::operator< (const graph_factt& other) const
{
  if (n!=other.n)
    return (n<other.n);
  if (m!=other.m)
    return (m<other.m);
  if (partition!=other.partition)
    return (partition<other.partition);
  if (derivation!=other.derivation)
    return (derivation<other.derivation);
  return false; // elements are equal
}

/*******************************************************************\

Function: graph_factt::operator==

  Inputs: Two graph_facts

 Outputs: 

 Purpose: Returns true if two facts are equal, false otherwise

\*******************************************************************/
bool graph_factt::operator==(const graph_factt& other) const
{
  return ((n==other.n) &&
          (m==other.m) &&
          (rel==other.rel) &&
          (partition==other.partition) &&
          (derivation==other.derivation));
}

/*******************************************************************\

Function: graph_factt::merge_relations

  Inputs: Two transitive relations

 Outputs: 

 Purpose: Merges two transitive relations

\*******************************************************************/
graph_factt::relationt graph_factt::merge_relations
(graph_factt::relationt r, graph_factt::relationt t)
{
  const unsigned merged=r^t;
  
  if (merged==(graph_factt::GREATER_THAN^graph_factt::GREATER_EQUAL_THAN))
    return graph_factt::GREATER_THAN;
  else if (!merged && r!=graph_factt::NOT_EQUAL)
    return r;
  else if (merged | graph_factt::EQUAL)
    return (graph_factt::relationt)(merged ^ graph_factt::EQUAL);
  else
  {
#ifdef DEBUG
    std::cerr << "Warning: merging relations resulted in UNKNOWN" 
              << std::endl;
#endif
    return graph_factt::UNKNOWN;
  }
}

/*******************************************************************\

Function: graph_factt::to_expression

  Inputs: The expression pool for the indices used by the fact

 Outputs: 

 Purpose: Converts a graph fact into an expression

\*******************************************************************/
exprt graph_factt::to_expression(const expression_poolt &pool) const
{
  exprt expression(relation_to_string(rel), typet("bool"));
  expression.copy_to_operands(pool[n]);
  expression.copy_to_operands(pool[m]);
  
  return expression;
}

/*******************************************************************\

Function: graph_interpolantt::graph_interpolantt

  Inputs: A fact

 Outputs: 

 Purpose: Constructor. Creates a graph interpolant with
          the given fact as only element of the chain.

\*******************************************************************/
graph_interpolantt::graph_interpolantt(const graph_factt& fact)
{
  chaint tmp(fact);
  chains.push_back(tmp);
}

/*******************************************************************\

Function: graph_interpolantt::chain_type

  Inputs: A chain, a threshold

 Outputs: 

 Purpose: Returns the whether the chain is an A or a B-chain

\*******************************************************************/
graph_interpolantt::chain_typet graph_interpolantt::chain_type(
  const graph_interpolantt::chaint& chain, 
  wordlevel_factt::partitiont threshold)
{
  return (chain.fact.partition<threshold)?
    (graph_interpolantt::A_CHAIN):(graph_interpolantt::B_CHAIN);
}

/*******************************************************************\

Function: graph_interpolantt::merge_chains

  Inputs: A graph interpolant, a threshold

 Outputs: Destructively updates both interpolants!

 Purpose: Concatenates two partial interpolants. 
          Returns true, if the adjacent chains were merged into one.

\*******************************************************************/
bool graph_interpolantt::merge_chains(
  graph_interpolantt& other, wordlevel_factt::partitiont threshold)
{
  bool merged=false;

  if(!other.chains.empty())
  {
    // check whether we can merge the back and front elements
    if (!chains.empty())
    {
      graph_interpolantt::chaint &back=chains.back();
      graph_interpolantt::chaint &front=other.chains.front();
          
      if(back.fact.m==front.fact.n && 
         chain_type(front, threshold)==chain_type(back, threshold))
      {
        back.fact.m=front.fact.m;
        back.fact.rel=
          graph_factt::merge_relations(front.fact.rel, back.fact.rel);
        // merge the premises and justifications
        back.justifications.splice(back.justifications.end(), 
                                   front.justifications);     
        back.premises.splice(back.premises.end(), front.premises);     
        back.current_premise.splice(back.current_premise.end(),
                                    front.current_premise);
        
        other.chains.pop_front(); 
        merged=true;
      }
    }

    // now concatenate the prefix and the suffix
    chains.splice(chains.end(), other.chains);
  }
  return merged;
}

/*******************************************************************\

Function: graph_interpolantt::mend_chain

  Inputs: A threshold

 Outputs: Destructively updates the chain of the interpolant

 Purpose: Merges the beginning and the end of the chains,
          if the respective nodes match. Returns true, if the
          chains have been modified.

\*******************************************************************/
bool graph_interpolantt::mend_chain(wordlevel_factt::partitiont threshold)
{
  if (chains.size()>1)
  {
    graph_interpolantt::chaint &front=chains.front();
    graph_interpolantt::chaint &back=chains.back();

    if (front.fact.n==back.fact.m &&
        chain_type(front, threshold)==chain_type(back, threshold))
    {
      front.fact.n=back.fact.n;
      front.fact.rel=
        graph_factt::merge_relations(back.fact.rel, front.fact.rel);
      
      front.justifications.splice(front.justifications.end(), 
                                  back.justifications);     
      front.premises.splice(front.premises.end(), back.premises);     
      front.current_premise.splice(front.current_premise.end(),
                                    back.current_premise);
      
      chains.pop_back();
      return true;
    }
  }
  return false;
}

/*******************************************************************\

Function: graph_interpolantt::lift_chains

  Inputs: A fact, a threshold

 Outputs: Destructively updates the interpolant and replaces
          the current chains with a single chain containing "fact"

 Purpose: Lifts the chains into the premises and justifications.
          The resulting chain is justified by the partial interpolant

\*******************************************************************/
void graph_interpolantt::lift_chains(
  const graph_factt& fact, wordlevel_factt::partitiont threshold)
{
  chaint result(fact);
  chain_typet premise_type=chain_type(result, threshold);

  for(chain_listt::iterator c_it=chains.begin();
      c_it!=chains.end(); ++c_it)
  {
    chaint& current=*c_it;

    result.premises.splice(result.premises.end(), current.premises);
    result.justifications.splice(result.justifications.end(), 
                                 current.justifications);

    // add the current condition to the respective lists
    if(premise_type!=chain_type(current, threshold))
    {
      result.current_premise.push_back(current.fact);

      if(premise_type==graph_interpolantt::B_CHAIN)
      {
        // Add the A-condition
        result.premises.push_back(current.fact);  
      }
      else
      {
        // Add the B-condition 
        justificationt justification(current.current_premise, current.fact);
        result.justifications.push_back(justification);
      }
    }
    else
    {
      result.current_premise.splice(result.current_premise.end(),
                                    current.current_premise);
    }
  }

  chains.clear();
  chains.push_back(result);
}

/*******************************************************************\

Function: graph_interpolantt::to_expression

  Inputs: A list of graph facts and an
          expression pool containing the nodes used 
          by the graph interpolant

 Outputs: 

 Purpose: Converts the list of graph facts in to a conjunctive
          expression

\*******************************************************************/
exprt graph_interpolantt::to_expression(
  const graph_fact_listt& facts, const expression_poolt& pool) const
{
  if(facts.size()==1)
    return facts.front().to_expression(pool);

  exprt conjunction("and", typet("bool"));
  
  for(graph_fact_listt::const_iterator f_it=facts.begin();
      f_it!=facts.end(); ++f_it)
  {
    conjunction.copy_to_operands(f_it->to_expression(pool));
  }
  
  if(facts.size()==0)
    conjunction.make_true();

  return conjunction;
}

/*******************************************************************\

Function: graph_interpolantt::to_expression

  Inputs: A justification and a
          expression pool containing the nodes used 
          by the graph interpolant

 Outputs: 

 Purpose: Converts the justification into a conjunction,
          where the justified element is negated

\*******************************************************************/
exprt graph_interpolantt::to_expression(
  const justificationt& justification, const expression_poolt& pool) const
{
  exprt negated=justification.second.to_expression(pool);
  negated.negate();
  
  if(justification.first.size()==0)
  {
    return negated;
  }

  exprt conjunction("and", typet("bool"));
  conjunction.copy_to_operands(to_expression(justification.first, pool));
  conjunction.copy_to_operands(negated);
  
  return conjunction;
}

/*******************************************************************\

Function: graph_interpolantt::to_expression

  Inputs: An expression pool containing the nodes used 
          by the graph interpolant

 Outputs: 

 Purpose: Converts the graph interpolant into an expression

\*******************************************************************/
exprt graph_interpolantt::to_expression(
  const chaint& chain, expression_poolt& pool)
{
  if(chain.justifications.size()==0)
    return to_expression(chain.premises,pool);
  
  exprt disjunction("or", typet("bool"));

  disjunction.copy_to_operands(to_expression(chain.premises,pool));

  for(justification_listt::const_iterator j_it=chain.justifications.begin();
      j_it!=chain.justifications.end(); ++j_it)
  {
    const justificationt &justification=*j_it;
    disjunction.copy_to_operands(to_expression(justification,pool));
  }

  simplify(disjunction, pool.ns);
  return disjunction;
}

/*******************************************************************\

Function: justificationst::add_justification

  Inputs: A fact and a vector of justifications.

 Outputs: 

 Purpose: Stores a number of justifications for a fact.
          Overwrites any existing justification for that fact.
          Destroys the content of the parameter 'justifications'

\*******************************************************************/
void justificationst::add_justification
(const graph_factt &fact, justificationt &justifications)
{
  justification_map[fact].swap(justifications);
}

/*******************************************************************\

Function: justificationst::add_justification

  Inputs: A fact and a list of graph_facts justifying the fact.

 Outputs: 

 Purpose: Stores a justification for a fact.
          Overwrites any existing justification for that fact.
          Destroys the content of the parameter 'facts'

\*******************************************************************/
void justificationst::add_justification
(const graph_factt &fact, graph_fact_listt &facts)
{
  justificationt &justification=justification_map[fact];
  justification.resize(1);
  justification.at(0).swap(facts);
}

/*******************************************************************\

Function: justificationst::has_justification

  Inputs: A fact

 Outputs: 

 Purpose: Returns true if the fact has a justification, false otherwise

\*******************************************************************/
bool justificationst::has_justification
(const graph_factt &fact)
{
  return (justification_map.find(fact)!=justification_map.end());
}

/*******************************************************************\

Function: justificationst::get_justification

  Inputs: A fact

 Outputs: 

 Purpose: Returns a vector of justifications for the fact.
          If there is no justification for this fact, an assertion
          will fail.
          USE CARFULLY! Returns a reference!

\*******************************************************************/
const justificationst::justificationt& 
justificationst::get_justification(const graph_factt &fact)
{
  justification_mapt::const_iterator it=justification_map.find(fact);
  assert(it!=justification_map.end());
  return it->second;
}

/*******************************************************************\

Function: justificationst::get_original_fact

  Inputs: A fact

 Outputs: 

 Purpose: Stores the corresponding original fact (as known by
          the other components of the decision procedure) for
          a fact that may have undergone a transformation
          (e.g., commutativity). Overwrites existing
          corresponding facts.

\*******************************************************************/
void justificationst::add_original_fact(
  const graph_factt &fact, const graph_factt& original)
{
  original_facts[fact]=original;
}

/*******************************************************************\

Function: justificationst::get_original_fact

  Inputs: A fact

 Outputs: 

 Purpose: Returns the corresponding original fact (as known by
          the other components of the decision procedure) for
          a fact that may have undergone a transformation
          (e.g., commutativity). Assertion fails if there
          is no corresponding fact.

\*******************************************************************/
graph_factt justificationst::get_original_fact(
  const graph_factt &fact)
{
  original_fact_mapt::const_iterator it=original_facts.find(fact);
  assert(it!=original_facts.end());
  return it->second;
}

/*******************************************************************\

Function: graph_based_interpolatort::find_chains

  Inputs: A path of facts.

 Outputs: 

 Purpose: Finds chains of facts in a path of facts.
          Asks the callback object for partial interpolants if
          the given fact in a chain is not a TOPLEVEL or THEORY fact.
 
\*******************************************************************/
void graph_based_interpolatort::find_chains
(const patht& path, wordlevel_factt::partitiont threshold, 
 graph_interpolator_callbackt& callback,
 graph_interpolantt& interpolant)
{
  graph_fact_listt facts;

  for(patht::const_iterator n_it=path.begin();
      n_it!=path.end(); n_it++)
  {
    patht::const_iterator m_it=n_it; m_it++;
    if (m_it!=path.end())
    {
      graph_factt fact;
      fact_from_edge (*n_it, *m_it, fact);
      facts.push_back(fact);
    }
  }

  find_chains(facts, threshold, callback, interpolant); 
}

/*******************************************************************\

Function: graph_based_interpolatort::find_chains

  Inputs: A sequence of facts.

 Outputs: 

 Purpose: Finds chains of facts in a path of facts.
          Asks the callback object for partial interpolants if
          the given fact in a chain is not a TOPLEVEL or THEORY fact.

\*******************************************************************/
void graph_based_interpolatort::find_chains
(const graph_fact_listt& facts, wordlevel_factt::partitiont threshold, 
 graph_interpolator_callbackt& callback,
 graph_interpolantt& interpolant)
{
  for(graph_fact_listt::const_iterator f_it=facts.begin();
      f_it!=facts.end(); f_it++)
  {
    const graph_factt &fact=*f_it;

    if (fact.derivation==wordlevel_factt::TOPLEVEL_FACT ||
        fact.derivation==wordlevel_factt::THEORY_FACT )
    {
      graph_interpolantt partial(fact);
      interpolant.merge_chains(partial, threshold);
    }
    else
    {
      graph_interpolantt partial;
      callback.get_interpolant(fact, threshold, partial);
      interpolant.merge_chains(partial, threshold);
    }
  }
}

/*******************************************************************\

Function: graph_based_interpolatort::get_interpolant

  Inputs: A fact, a partition, an interpolant data structure

 Outputs: The premise of the given fact is computed
          and the the required justifications for the premise
          are added to the partial interpolant

 Purpose: Compute the premise and partial interpolant of a fact.
          Returns true if the interpolant is a partial interpolant
          (i.e., the current fact is not a contradiction)

\*******************************************************************/
bool graph_based_interpolatort::get_interpolant(
  const graph_factt& fact, wordlevel_factt::partitiont threshold,
  graph_interpolator_callbackt& callback,
  graph_interpolantt& interpolant)
{
  graph_factt actual_fact;

  assert(fact.derivation==wordlevel_factt::INEQUALITY_INTERPOLATOR ||
         fact.derivation==wordlevel_factt::DISEQUALITY_INTERPOLATOR);

  bool partial=get_actual_fact(fact, actual_fact);

  if(justifications.has_justification(actual_fact))
  {
    const justificationst::justificationt &justification=
      justifications.get_justification(actual_fact);
    const graph_fact_listt &facts=justification[0];
    find_chains(facts, threshold, callback, interpolant);
  }
   
  graph_interpolantt link;
  if(actual_fact.derivation==wordlevel_factt::TOPLEVEL_FACT ||
     actual_fact.derivation==wordlevel_factt::THEORY_FACT)
  {
    link=graph_interpolantt(actual_fact);
  }
  else
  {
    callback.get_interpolant(actual_fact, threshold, link);
  }

  interpolant.merge_chains(link, threshold);
  interpolant.mend_chain(threshold);
  
  graph_interpolantt::chaint &front=interpolant.chains.front();
  graph_interpolantt::chaint &back=interpolant.chains.back();

  if (front.fact.n==back.fact.m && interpolant.chains.size()==1) 
  {
    switch(front.fact.rel)
    {
    case graph_factt::EQUAL:
    case graph_factt::GREATER_EQUAL_THAN:
      // the chain implies equality
      front.fact.n=0; front.fact.m=0;
      front.fact.rel=graph_factt::EQUAL;
      break;
    case graph_factt::GREATER_THAN:
    case graph_factt::NOT_EQUAL:
      // this is a closed contradictory cycle
      front.fact.n=0; front.fact.m=0;
      front.fact.rel=graph_factt::NOT_EQUAL;
      break;
    case graph_factt::UNKNOWN:
    default: // UNKNOWN?
      assert (false);  
    }
  }

  interpolant.lift_chains(fact, threshold);
  return partial;
}

/*******************************************************************\

Function: inequality_interpolatort::add_fact

  Inputs: 

 Outputs: Returns true if the fact was already known or is 
          not helpful

 Purpose: Adds a graph fact to the inequality interpolator fact base

\*******************************************************************/
bool inequality_interpolatort::add_fact(const graph_factt& fact)
{
  if(inconsistent)
    return true;

  const unsigned max=std::max(fact.n, fact.m);
  if (max>=inequality_graph.size())
    inequality_graph.resize(max+1);

  if (inequality_graph.has_edge(fact.n, fact.m))
  {
    inequality_edget &edge=inequality_graph.edge(fact.n, fact.m);
    if(edge.rel==fact.rel || 
       edge.rel==graph_factt::GREATER_THAN) // avoid weakening
      return true;

    edge.rel=fact.rel;
    edge.derivation=fact.derivation;
    edge.partition=fact.partition;
  }
  else
  {
    inequality_graph.add_edge(fact.n, fact.m);
    inequality_edget &edge=inequality_graph.edge(fact.n, fact.m);
    edge.rel=fact.rel;
    edge.derivation=fact.derivation;
    edge.partition=fact.partition;
  }
  return false;
}

/*******************************************************************\

Function: inequality_interpolatort::fact_from_edge

  Inputs: Two node indices, a target fact

 Outputs: A fact corresponding to the given edge

 Purpose: 

\*******************************************************************/
void inequality_interpolatort::fact_from_edge
(unsigned n, unsigned m, graph_factt& fact)
{
  assert (inequality_graph.has_edge(n, m));
  inequality_grapht::edget &edge=inequality_graph.edge(n, m);

  fact.n=n;
  fact.m=m;
  fact.rel=edge.rel;
  fact.derivation=edge.derivation;
  fact.partition=edge.partition;
}

/*******************************************************************\

Function: inequality_interpolatort::infer

  Inputs: superordinate interpolator to report inferred equalities to

 Outputs: returns false, if fact base is contradictory

 Purpose: Compute the SCCs of the inequality graph. 
          If an SCC contains a > relation, we have a contradiction.
          For all other SCCs, all contained nodes are equal 
          (we add an = relation for each >= relation in the SCC)

\*******************************************************************/
bool inequality_interpolatort::infer(graph_interpolator_callbackt& c)
{
  unsigned index;
  std::vector<unsigned> scc;

  inequality_graph.SCCs(scc);

  // sweep run: search for contradictions
  for (index=0; index<inequality_graph.size(); index++)
  {
    const inequality_grapht::nodet &node=inequality_graph[index];
    for(inequality_grapht::edgest::const_iterator 
          e_it=node.out.begin();
        e_it!=node.out.end();
        e_it++)
    {
      unsigned dest=e_it->first;
      if (scc[index]==scc[dest] &&
          e_it->second.rel==graph_factt::GREATER_THAN)
      {
        contradiction.n=index;
        contradiction.m=dest;
        contradiction.rel=graph_factt::GREATER_THAN;
        contradiction.derivation=e_it->second.derivation;
        contradiction.partition=e_it->second.partition;

        // remember the justification, this is part of the proof!
        remember_justification(contradiction);

        inconsistent=true;

        graph_factt fact;
        fact.n=index; fact.m=index;
        fact.rel=graph_factt::GREATER_THAN;
        fact.derivation=wordlevel_factt::INEQUALITY_INTERPOLATOR;
        fact.partition=e_it->second.partition;
        c.report_contradiction(fact);

        return false;
      }
    }
  }

  // inference run: add inferred equalities
  for (index=0; index<inequality_graph.size(); index++)
  {
    const inequality_grapht::nodet &node=inequality_graph[index];
    for(inequality_grapht::edgest::const_iterator 
          e_it=node.out.begin();
        e_it!=node.out.end();
        e_it++)
    {
      unsigned dest=e_it->first;
      if (scc[index]==scc[dest])
      {
        graph_factt fact;
        fact.n=index; fact.m=dest;
        fact.rel=graph_factt::EQUAL;
        fact.derivation=wordlevel_factt::INEQUALITY_INTERPOLATOR;
        fact.partition=e_it->second.partition;
        c.add_fact(fact);

        // remember the justification, this is part of the proof!
        remember_justification(fact);
      }
    }
  }
  
#ifdef DEBUG
  std::cout << "inequality: " << std::endl;
  inequality_graph.output_dot(std::cout);
#endif

  return true;
}

/*******************************************************************\

Function: inequality_interpolatort::trace_fact

  Inputs: A fact

 Outputs: A corresponding path

 Purpose: Find the trace of facts that implies the given fact

\*******************************************************************/
graph_based_interpolatort::patht&
inequality_interpolatort::trace_fact(const graph_factt &fact)
{
  patht &path=path_cache[fact]; // creates an empty path if necessary
  
  if (path.size()==0)
    inequality_graph.shortest_path(fact.m, fact.n, path);
  
  return path;
}

/*******************************************************************\

Function: inequality_interpolatort::get_actual_fact

  Inputs: A fact, a target fact

 Outputs: 

 Purpose: Given a fact derived by the inequality interpolator,
          return the fact that's "associated" to that fact
          (i.e., either the fact that caused
           a contradiction, or an edge that was inferred by
           the interpolator). 
          Helper function for get_interpolant.
          Returns false if the fact stems from an inconsistency,
          true otherwise

\*******************************************************************/
bool inequality_interpolatort::get_actual_fact
(const graph_factt& fact, graph_factt& actual_fact)
{
  assert(fact.derivation==wordlevel_factt::INEQUALITY_INTERPOLATOR);

  if (fact.n==fact.m) // this is a contradiction
  {
    assert (inconsistent);
    actual_fact=contradiction;
    return false;
  }
  else
  {
    assert(fact.rel==graph_factt::EQUAL || 
           fact.rel==graph_factt::GREATER_EQUAL_THAN);
    assert(inequality_graph.has_edge(fact.n, fact.m)||
           inequality_graph.has_edge(fact.m, fact.n));
    if (inequality_graph.has_edge(fact.n, fact.m))
    {
      actual_fact.n=fact.n; actual_fact.m=fact.m;
    }
    else // other direction
    {
      actual_fact.n=fact.m; actual_fact.m=fact.n;
    }
    inequality_grapht::edget &edge=
      inequality_graph.edge(actual_fact.n, actual_fact.m);
    actual_fact.rel=edge.rel;
    actual_fact.partition=edge.partition;
    actual_fact.derivation=edge.derivation;
    return true;
  }
}

/*******************************************************************\

Function: disequality_grapht::add_indirect_edge

  Inputs: 

 Outputs: 

 Purpose: Adds an edge with indirection information.
          Returns false if an edge was added and true
          if an existing edge was not overwritten.

\*******************************************************************/
bool disequality_grapht::add_indirect_edge(
  unsigned start, unsigned end, unsigned indirection, 
  wordlevel_factt::derivationt derivation)
{
  if (has_edge(start, end) || has_edge(end, start))
    return true;

  add_edge(start, end);
  edget &shortcut=edge(start, end);
  shortcut.indirection=indirection;
  shortcut.derivation=derivation;
  return false;
}

/*******************************************************************\

Function: disequality_grapht::triangulate

  Inputs: n_root: the higher ranked representative in make_union
          m_root: the lower ranked representative in make_union
          n, m: the respective original node indices

 Assumes: The edges n=n_root, m=m_root, n=m already exist

 Outputs: 

 Purpose: Triangulates a rectangle (occuring in make_union) of 
          vertices by adding the appropriate new fact edges to 
          the graph. The runtime of this operation is O(1).

\*******************************************************************/
void disequality_grapht::triangulate
(unsigned n, unsigned n_root, unsigned m, unsigned m_root)
{
  assert (n!=m && n_root!=m_root);

  if (n==n_root) // it follows that m!=n_root
  {
    if (m!=m_root)
      add_indirect_edge(m_root, n_root, m, 
                        wordlevel_factt::DISEQUALITY_INTERPOLATOR);
  }
  else 
  {
    // we might have to add 2 edges, depending on whether m==m_root
    if (m!=n_root) 
    {
      add_indirect_edge(m, n_root, n, 
                        wordlevel_factt::DISEQUALITY_INTERPOLATOR); 
      vertices[m].parent=n_root;
    }
    if (m!=m_root)
    {
      add_indirect_edge(m_root, n_root, m, 
                        wordlevel_factt::DISEQUALITY_INTERPOLATOR);
    }
  }
}

/*******************************************************************\

Function: disequality_grapht::register_callback

  Inputs: A pointer to a callback object

 Outputs: 

 Purpose: registers a callback for merging equivalence classes

\*******************************************************************/
void disequality_grapht::register_callback(union_callbackt *callback)
{
  callbacks.push_back(callback);
}


/*******************************************************************\

Function: disequality_grapht::run_merge_callbacks

  Inputs: Executes all registered callback functions 

 Outputs: 

 Purpose: Called when two equivalence classes are merged.
          The first argument is the old representative,
          the second argument is the new representative.

\*******************************************************************/
void disequality_grapht::run_merge_callbacks(unsigned n, unsigned m)
{
  for(std::list<union_callbackt *>::iterator c_it=callbacks.begin();
      c_it!=callbacks.end(); ++c_it)
  {
    (*c_it)->merge(n, m);
  }
}

/*******************************************************************\

Function: disequality_grapht::run_add_callbacks

  Inputs: Executes all registered "add" callback functions 

 Outputs: 

 Purpose: Called when a new node is added 

\*******************************************************************/
void disequality_grapht::run_add_callbacks(unsigned n)
{
  for(std::list<union_callbackt *>::iterator c_it=callbacks.begin();
      c_it!=callbacks.end(); ++c_it)
  {
    (*c_it)->add_class(n);
  }
}


/*******************************************************************\

Function: disequality_grapht::make_set

  Inputs: A node is added as a singleton set 
          (no change if it already exists)

 Outputs: 

 Purpose: 

\*******************************************************************/
void disequality_grapht::make_set(unsigned node)
{
  if(node>=vertices.size())
    vertices.resize(node+1);
  if(node>=size())
    resize(node+1);

  run_add_callbacks(node);
}


/*******************************************************************\

Function: disequality_grapht::make_union

  Inputs: A fact that will be added to the union find data structure

 Outputs: The new representative for both nodes

 Purpose: 

\*******************************************************************/
unsigned disequality_grapht::make_union(const graph_factt& fact)
{
  assert(fact.rel==graph_factt::EQUAL);

  // add original edge to graph
  add_edge(fact.n, fact.m);
  edge(fact.n, fact.m).derivation=fact.derivation;
  edge(fact.n, fact.m).partition=fact.partition;

  unsigned n_root=find(fact.n);
  unsigned m_root=find(fact.m);

  if (n_root==m_root) 
    return n_root; // already belong to the same set

  if (vertices[n_root].rank > vertices[m_root].rank)
  {
    vertices[n_root].rank+=vertices[m_root].rank;
    vertices[m_root].parent=n_root;
    vertices[m_root].root=false;
    triangulate(fact.n, n_root, fact.m, m_root);
    run_merge_callbacks(m_root, n_root);
    return n_root;
  }
  else
  {
    vertices[m_root].rank+=vertices[n_root].rank;
    vertices[n_root].parent=m_root;
    vertices[n_root].root=false;
    triangulate(fact.m, m_root, fact.n, n_root);
    run_merge_callbacks(n_root, m_root);
    return m_root;
  }
}

/*******************************************************************\

Function: disequality_grapht::find

  Inputs: A node index

 Outputs: The representative of that node

 Purpose: Finds the representative of a node.
          Performs path compression and adds shortcut edges 

\*******************************************************************/
unsigned disequality_grapht::find(unsigned current)
{
  if (current>=vertices.size())
    return current; // we don't know about this edge

  disequality_grapht::vertext &vertex=vertices[current];
  if (vertex.root)
    return current;

  assert(has_edge(current, vertex.parent)||
         has_edge(vertex.parent, current));

  unsigned representative=find(vertex.parent);
  
  // do we have to create a new fact?
  if (vertex.parent!=representative)
  {
    add_indirect_edge(current, representative, vertex.parent,
                      wordlevel_factt::DISEQUALITY_INTERPOLATOR);
    // path compression!
    vertex.parent=representative;
  }

  return representative;
}

/*******************************************************************\

Function: disequality_grapht::trace_fact

  Inputs: Two indices and an empty path

 Outputs: The edges that are responsible for the equality

 Purpose: The edges reported by the function represent facts
          that have been added using add_fact (i.e., not facts
          internally inferred by disequality_grapht)

\*******************************************************************/
void disequality_grapht::trace_fact
(unsigned n, unsigned m, patht& path)
{
  unsigned indirection;

  assert(n!=m);

  if (has_edge(n, m)||has_edge(m, n))
  {
    // deal with symmetry
    edget &e=has_edge(n,m)?edge(n,m):edge(m,n);

    if (e.derivation!=wordlevel_factt::DISEQUALITY_INTERPOLATOR)
    {
      path.push_back(n);
      path.push_back(m);
      return;
    }

    indirection=e.indirection;
  }
  else
  {
    indirection=find(n);
    assert(indirection==find(m));
  }

  trace_fact(n, indirection, path);
  path.pop_back(); // eliminate intermediate node
  trace_fact(indirection, m, path);
}


/*******************************************************************\

Function: disequality_interpolatort::add_fact

  Inputs: Adds a graph fact to the disequality interpolator fact base

 Outputs: Returns true if the fact was already known

 Purpose: 

\*******************************************************************/
bool disequality_interpolatort::add_fact(const graph_factt& fact)
{
  if(inconsistent)
    return true;

  union_find.make_set(fact.n);
  union_find.make_set(fact.m);

  if (fact.rel==graph_factt::EQUAL)
  {
    if (!union_find.same_set(fact.n, fact.m))  // avoid duplicate work
    {
      union_find.make_union(fact);
      return false;
    }
    else
      return true;
  }
  else
  {
    assert(fact.rel==graph_factt::NOT_EQUAL);
    return !(inequality_facts.insert(fact)).second;
  }
}

/*******************************************************************\

Function: disequality_interpolatort::fact_from_edge

  Inputs: Two node indices, a target fact

 Outputs: A fact corresponding to the given edge

 Purpose: 

\*******************************************************************/
void disequality_interpolatort::fact_from_edge
(unsigned n, unsigned m, graph_factt& fact)
{
  assert (union_find.has_edge(n, m)||union_find.has_edge(m, n));
  disequality_grapht::edget &edge=
    union_find.has_edge(n, m)?union_find.edge(n, m):union_find.edge(m, n);

  fact.n=n;
  fact.m=m;
  fact.rel=graph_factt::EQUAL;
  fact.derivation=edge.derivation;
  fact.partition=edge.partition;
}

/*******************************************************************\

Function: disequality_interpolatort::infer

  Inputs: superordinate interpolator to report contradictions to

 Outputs: returns false, if fact base is contradictory

 Purpose: 

\*******************************************************************/
bool disequality_interpolatort::infer(graph_interpolator_callbackt& c)
{
  // do queries with the postponed inequalities
  for(std::set<graph_factt>::const_iterator i_it=inequality_facts.begin();
      i_it!=inequality_facts.end(); ++i_it)
  {
    const graph_factt &fact=*i_it;

    if (union_find.find(fact.n)==union_find.find(fact.m))
    {
      contradiction=fact; // remember this

      // remember the justifications, they are part of the proof!
      remember_justification(contradiction);

      graph_factt reversed=fact;
      reversed.n=fact.m; reversed.m=fact.n;
      assert(reversed.rel==graph_factt::NOT_EQUAL);
      remember_justification(reversed);

      inconsistent=true;

      graph_factt contra;
      contra.n=fact.n; contra.m=fact.n;
      contra.rel=graph_factt::NOT_EQUAL;
      contra.derivation=wordlevel_factt::DISEQUALITY_INTERPOLATOR;
      c.report_contradiction(contra);

      return false;
    }
  }

#ifdef DEBUG
  std::cout << "union find: " << std::endl;
  union_find.output_dot(std::cout);
#endif
  return true;
}

/*******************************************************************\

Function: disequality_interpolatort::trace_fact

  Inputs: A fact

 Outputs: A corresponding path

 Purpose: Find the chain of facts that implies the given equality.

\*******************************************************************/
graph_based_interpolatort::patht& 
disequality_interpolatort::trace_fact (const graph_factt &fact)
{
  patht &path=path_cache[fact]; // creates an empty path if necessary

  if (path.size()==0)
    union_find.trace_fact(fact.m, fact.n, path);

  return path;
}

/*******************************************************************\

Function: graph_based_interpolatort::remember_justification

  Inputs: A fact that has just been inferred

 Outputs: 

 Purpose: Stores the sequence of facts justifying the given fact

\*******************************************************************/
void graph_based_interpolatort::remember_justification(
  const graph_factt &fact)
{
  if(!justifications.has_justification(fact))
  {
    graph_fact_listt facts;

    patht path=trace_fact(fact);
    
    for(patht::const_iterator n_it=path.begin();
        n_it!=path.end(); n_it++)
    {
      patht::const_iterator m_it=n_it; m_it++;
      if (m_it!=path.end())
      {
        graph_factt fact;
        fact_from_edge(*n_it, *m_it, fact);
        facts.push_back(fact);
        
        if(fact.derivation==derivation_type())
        {
          graph_factt actual_fact;
          get_actual_fact(fact, actual_fact);
          justifications.add_original_fact(fact, actual_fact);
        }
      }
    }
    
    if(facts.size()>0)
      justifications.add_justification(fact, facts);
  }
}

/*******************************************************************\

Function: disequality_interpolatort::get_actual_fact

  Inputs: A fact, a target fact

 Outputs: 

 Purpose: Given a fact derived by the disequality interpolator,
          return the fact that's "associated" to that fact
          Helper function for get_interpolant.
          Returns false if the fact stems from an inconsistency,
          true otherwise

\*******************************************************************/
bool disequality_interpolatort::get_actual_fact
(const graph_factt& fact, graph_factt& actual_fact)
{
  assert(fact.derivation==wordlevel_factt::DISEQUALITY_INTERPOLATOR);

  if(fact.n==fact.m)
  {
    assert (fact.n==contradiction.n && inconsistent);
    actual_fact=contradiction;
    return false;
  }

  assert(union_find.find(fact.n)==union_find.find(fact.m));

  actual_fact=fact;
  return true;
}

/*******************************************************************\

Function: congruencest::add_fact

  Inputs: A graph_fact representing a congruence edge. 

 Outputs: 

 Purpose: Adds the justifying paths to the map of congruences.
          

\*******************************************************************/
void congruencest::add_fact(const graph_factt &fact)
{
  const congruencet congruence(fact.n, fact.m);
  
  if(congruence_map.find(congruence)==congruence_map.end())
  {
    const exprt left=expression_pool[fact.n];
    const exprt right=expression_pool[fact.m];

    assert(left.has_operands() && right.has_operands() &&
           left.operands().size()==right.operands().size());

    // create a new justification
    pathst &paths=congruence_map[congruence];
    paths.resize(left.operands().size());

    exprt::operandst::const_iterator l_it=left.operands().begin();
    exprt::operandst::const_iterator r_it=right.operands().begin();
    unsigned count=0;

    graph_factt parent;
    parent.rel=graph_factt::EQUAL;
    parent.derivation=wordlevel_factt::DISEQUALITY_INTERPOLATOR;
    
    for(; l_it!=left.operands().end(); ++l_it, ++r_it, ++count)
    {
      // construct a swapped fact for trace_fact!
      parent.m=expression_pool.number(*l_it);
      parent.n=expression_pool.number(*r_it);
      if(parent.n!=parent.m)
      {
        paths[count]=disequality_interpolator.trace_fact(parent);
      }
    }
  }
}

/*******************************************************************\

Function: congruencest::add_fact

  Inputs: A graph_fact representing a congruence edge and 
          two respective indices of terms that are equal.

 Outputs: 

 Purpose: Add a congruence edge and the respective justification
          to the congruences. Adds the justification to the
          congruence edge if the edge already exists.

\*******************************************************************/
void congruencest::add_fact(
  const graph_factt &fact,
  unsigned left, unsigned right)
{
  const congruencet congruence(fact.n, fact.m);

  graph_factt parent;
  parent.rel=graph_factt::EQUAL;
  parent.derivation=wordlevel_factt::DISEQUALITY_INTERPOLATOR;
  parent.m=left;
  parent.n=right;

  pathst &paths=congruence_map[congruence];
  
  if(congruence_map.find(congruence)==congruence_map.end())
    paths.resize(1);
  else
    paths.resize(paths.size()+1);

  if(left!=right)
    paths[paths.size()-1]=disequality_interpolator.trace_fact(parent);
}

/*******************************************************************\

Function: congruencest::get_justification

  Inputs: A graph_fact representing a congruence edge. 

 Outputs: Returns the paths justifying a congruence.

 Purpose: Get the paths justifying a congruence. This 
          function will fail with an assertion if the
          congruence is unjustified
          

\*******************************************************************/
const congruencest::pathst& congruencest::get_justification(
  const graph_factt &fact)
{
  const congruencet congruence(fact.n, fact.m);

  congruence_mapt::const_iterator it=congruence_map.find(congruence);

  if(it!=congruence_map.end())
    return (it->second);
 
  const congruencet reversed(fact.m, fact.n);
  it=congruence_map.find(reversed);
  
  assert(it!=congruence_map.end());
  
  // construct reversed justifications and insert it
  std::pair<congruencest::congruence_mapt::iterator, bool> insertion=
    congruence_map.insert(std::pair<congruencest::congruencet,
                          congruencest::pathst>
                          (congruence, it->second));
  
  assert(insertion.second);
  
  congruencest::pathst &paths=(insertion.first)->second;
  for (unsigned position=0; position<paths.size(); ++position)
  {
    paths[position].reverse();
  }
  
  return paths;
}

/*******************************************************************\

Function: uif_interpolatort::lookup

  Inputs: A node index a 'constant' indexing an equivalence class

 Outputs: An element from the equivalence class indexed by
          the given constant (in result). Returns true if
          there is no corresponding equivalence class, 
          false otherwise.

 Purpose: Used by the congruence closure algorithm.

\*******************************************************************/
bool uif_interpolatort::lookup(unsigned n, unsigned &result)
{
  hash_map_cont<unsigned, unsigned>::const_iterator it;
  
  it=lookup_table.find(n);

  if(it==lookup_table.end())
    return true;

  result=it->second;
  return false;
}

/*******************************************************************\

Function: uif_interpolatort::add_class

  Inputs: 

 Outputs: 

 Purpose: 

\*******************************************************************/
void uif_interpolatort::add_class(unsigned index)
{
  colour_ranget range;
  expression_pool.get_colour(index, range);
  exprt expr=expression_pool[index];

  if(index>=processed.size())
    processed.resize(index+1, false);
  if(processed[index])
    return;
  processed[index]=true;

  std::list<unsigned> representatives;

  Forall_operands(e_it, expr)
  {
    unsigned node, representative;

    node=expression_pool.number(*e_it, range);
    representative=disequality_interpolator.get_representative(node);
    representatives.push_back(representative);
    
    *e_it=expression_pool[representative];
  }

  unsigned new_index=expression_pool.number(expr);

  lookup_tablet::const_iterator t_it=lookup_table.find(new_index);
  if(t_it!=lookup_table.end())
  {
    if(t_it->second!=index)
    {
      // add new equality to pending
      pending.push_back(graph_factt());
      graph_factt &fact=pending.back();
      fact.derivation=wordlevel_factt::UIF_INTERPOLATOR;
      fact.rel=graph_factt::EQUAL;
      fact.n=index; fact.m=t_it->second;

      congruences.add_fact(fact);
    }
  }
  else
  {
    lookup_table[new_index]=index;
    for(std::list<unsigned>::const_iterator r_it=representatives.begin();
        r_it!=representatives.end(); ++r_it)
    {
      use_list[*r_it].push_back(index);
    }
  }
}

/*******************************************************************\

Function: uif_interpolatort::merge

  Inputs: A representative for the old equivalence class
          and a representative for the new equivalence class

 Outputs: 

 Purpose: Called by the union find data structure when two
          equivalence classes are merged. Updates all indices
          for the affected equivalence classes.

\*******************************************************************/
void uif_interpolatort::merge(
  unsigned oldrep, unsigned newrep)
{
  assert(oldrep!=newrep);

  // new list needs to be added before obtaining the iterator
  std::list<unsigned> &new_list=use_list[newrep];

  const use_listt::iterator u_it=use_list.find(oldrep);
  if(u_it==use_list.end())
    return;

  const std::list<unsigned> &old_list=u_it->second;

  for(std::list<unsigned>::const_iterator l_it=old_list.begin();
      l_it!=old_list.end(); ++l_it)
  {
    unsigned index=*l_it;
    colour_ranget range;
    expression_pool.get_colour(index, range);
    exprt expr=expression_pool[index];
    
    Forall_operands(e_it, expr)
    {
      unsigned node, representative;
      
      node=expression_pool.number(*e_it, range);
      representative=disequality_interpolator.get_representative(node);
      
      *e_it=expression_pool[representative];
    }
    
    unsigned new_index=expression_pool.number(expr);
    
    lookup_tablet::const_iterator t_it=lookup_table.find(new_index);
    if(t_it!=lookup_table.end())
    {
      if(t_it->second!=index)
      {
        // add new equality to pending
        pending.push_back(graph_factt());
        graph_factt &fact=pending.back();
        fact.derivation=wordlevel_factt::UIF_INTERPOLATOR;
        fact.rel=graph_factt::EQUAL;
        fact.n=index; fact.m=t_it->second;

        congruences.add_fact(fact);
      }
    }
    else
    {
      lookup_table[new_index]=index;
      new_list.push_back(index);
    }
  }

  use_list.erase(u_it); // this is not absolutely necessary
}

/*******************************************************************\

Function: uif_interpolatort::infer

  Inputs: 

 Outputs: 

 Purpose: Adds the newly inferred equalities. Always returns true
          (i.e., never infers a contradiction)

\*******************************************************************/
bool uif_interpolatort::infer(graph_interpolator_callbackt& callback)
{
  // process pending equalities
  for(graph_fact_listt::const_iterator p_it=pending.begin();
      p_it!=pending.end(); ++p_it)
  {
    const graph_factt &fact=*p_it;
    callback.add_fact(fact);
  }

  return true;
}

/*******************************************************************\

Function: uif_interpolatort::colour_fact

  Inputs: 

 Outputs: 

 Purpose: Colours a fact, splitting it into two facts if
          necessary

\*******************************************************************/
void uif_interpolatort::colour_fact(
  const graph_factt& fact, 
  wordlevel_factt::partitiont threshold,
  std::list<graph_factt>& facts,
  std::list<graph_interpolantt>& interpolants)
{
  // check if the fact is already colourable
  colour_ranget n_range, m_range;

  expression_pool.get_colour(fact.n, n_range);
  expression_pool.get_colour(fact.m, m_range);

  facts.push_back(fact);

  if(n_range.first<threshold && m_range.first<threshold)
  {
    facts.front().partition=n_range.first;
    interpolants.resize(1);
  }
  else if(n_range.second>=threshold && m_range.second>=threshold)
  {
    facts.front().partition=m_range.second;
    interpolants.resize(1);
  }
  else 
  {
    facts.push_back(fact); // we need a second copy of this fact
    interpolants.resize(2);
    if(n_range.second<threshold) // we are on the A side
    {
      assert(m_range.first>=threshold);
      facts.front().partition=n_range.second;
      facts.back().partition=m_range.first;
    }
    else
    {
      assert(m_range.second<threshold);
      facts.front().partition=n_range.first;
      facts.back().partition=m_range.second;
    }
  }
}

/*******************************************************************\

Function: uif_interpolatort::get_interpolant

  Inputs: 

 Outputs: 

 Purpose: Returns a partial interpolant for an uif equality.

\*******************************************************************/
bool uif_interpolatort::get_interpolant(
  const graph_factt& fact, 
  wordlevel_factt::partitiont threshold,
  graph_interpolator_callbackt& callback, 
  graph_interpolantt& interpolant)
{
  assert(fact.derivation==wordlevel_factt::UIF_INTERPOLATOR);
  assert(fact.rel==graph_factt::EQUAL || 
         fact.rel==graph_factt::GREATER_EQUAL_THAN);

  std::list<graph_factt> facts;
  std::list<graph_interpolantt> interpolants;
  // the following operation 
  colour_fact(fact, threshold, facts, interpolants);

  graph_interpolantt::chain_typet left_colour=
    (facts.front().partition<threshold)?
    (graph_interpolantt::A_CHAIN):(graph_interpolantt::B_CHAIN);

  exprt left=expression_pool[fact.n]; // we may change this expression
  const exprt right=expression_pool[fact.m]; // but not this one

  assert(left.has_operands() && right.has_operands());

  const congruencest::pathst &paths=congruences.get_justification(fact);

  assert(left.operands().size()==paths.size() &&
         right.operands().size()==paths.size());

  exprt::operandst::iterator l_it=left.operands().begin();
  exprt::operandst::const_iterator r_it=right.operands().begin();

  for(unsigned count=0; l_it!=left.operands().end(); 
      ++l_it, ++r_it, ++count)
  {
    if(paths[count].size()!=0)
    {
      const graph_based_interpolatort::patht &path=paths[count];

      graph_interpolantt partial;
      disequality_interpolator.find_chains(path, threshold, 
                                           callback, partial);

      graph_interpolantt::chaint &front=partial.chains.front();
      
      if(interpolants.size()>1 &&
         left_colour==graph_interpolantt::chain_type(front, threshold))
      {
        *l_it=expression_pool[front.fact.m];
        interpolants.front().chains.splice
          (interpolants.front().chains.end(),
           partial.chains,
           partial.chains.begin());
      }

      interpolants.back().chains.splice
        (interpolants.back().chains.end(), partial.chains);
    }
    else
      assert(*l_it==*r_it);
  }

  if(interpolants.size()>1)
  {
    facts.front().m=facts.back().n=expression_pool.number(left);
  }

  // now lift and merge the interpolants
  std::list<graph_interpolantt>::iterator i_it=interpolants.begin();
  std::list<graph_factt>::const_iterator f_it=facts.begin();
  for(; f_it!=facts.end(); ++f_it, ++i_it)
  {
    graph_interpolantt &itp=*i_it;
    itp.lift_chains(*f_it, threshold);
    interpolant.merge_chains(itp, threshold);
  }
  
  return true;
}


/*******************************************************************\

Function: constant_propagationt::add_class

  Inputs: 

 Outputs: 

 Purpose: Store information about constants

\*******************************************************************/
void constant_propagationt::add_class(unsigned index)
{
  if(expression_pool.is_constant(index))
  {
    if(index>=representative_constants.size())
      representative_constants.resize(index+1);
    
    representative_constants[index].has_representative_constant=true;
    representative_constants[index].representative_constant=index;
  }
}

/*******************************************************************\

Function: constant_propagationt::merge

  Inputs: 

 Outputs: 

 Purpose: Merges the representative constant information of
          two nodes, where "newrep" denotes the node that will
          be the new representative.
          Furthermore, generates a disequality if the representative 
          constants of the two roots are different.

\*******************************************************************/
void constant_propagationt::merge(unsigned oldrep, unsigned newrep)
{
  unsigned max=std::max(oldrep,newrep);
  if(max>=representative_constants.size())
    representative_constants.resize(max+1);

  if (representative_constants[newrep].has_representative_constant)
  {
    // the following check for inequality should be more elaborate!
    if (representative_constants[oldrep].has_representative_constant)
    {
      decision_proceduret::resultt cmp=
        expression_pool.compare_constants(
          representative_constants[newrep].representative_constant,
          representative_constants[oldrep].representative_constant);
      
      if(cmp==decision_proceduret::D_UNSATISFIABLE)
      {
        graph_factt fact;
        fact.rel=graph_factt::NOT_EQUAL;
        fact.n=representative_constants[newrep].representative_constant;
        fact.m=representative_constants[oldrep].representative_constant;
        fact.derivation=wordlevel_factt::THEORY_FACT;
        fact.partition=0;
        inferred_disequalities.push(fact);
      }
    }
  }
  else
  {
    representative_constants[newrep].has_representative_constant=
      representative_constants[oldrep].has_representative_constant;
    representative_constants[newrep].representative_constant=
      representative_constants[oldrep].representative_constant;
  }
}

/*******************************************************************\

Function: constant_propagationt::get_constant_info

  Inputs: A node index and its representative root

 Outputs: 

 Purpose: Gets the representative constant of a node.
          Returns true if the node does not have a representative
          constant. This function calls find.

\*******************************************************************/
bool constant_propagationt::get_constant_info(
  unsigned index, unsigned &cindex)
{
  if(index>=representative_constants.size())
    return true;

  unsigned representative=
    disequality_interpolator.get_representative(index);

  const constant_infot &constant_info=
    representative_constants[representative];
  
  if(constant_info.has_representative_constant)
  {
    cindex=constant_info.representative_constant;
    return false;
  }
  return true;
}

/*******************************************************************\

Function: constant_propagationt::get_interpolant

  Inputs: 

 Outputs: 

 Purpose: Returns a partial interpolant for a fact inferred by
          means of constant propagation.

\*******************************************************************/
bool constant_propagationt::get_interpolant(
  const graph_factt& fact, 
  wordlevel_factt::partitiont threshold,
  graph_interpolator_callbackt& callback, 
  graph_interpolantt& interpolant)
{
  assert(fact.derivation==wordlevel_factt::CONSTANT_PROPAGATION);

  const exprt left=expression_pool[fact.n]; 
  const exprt right=expression_pool[fact.m]; 

  assert(left.has_operands() && right.has_operands());

  const congruencest::pathst& paths=congruences.get_justification(fact);

  assert(left.operands().size()==paths.size() &&
         right.operands().size()==paths.size());
  
  exprt::operandst::const_iterator l_it=left.operands().begin();
  exprt::operandst::const_iterator r_it=right.operands().begin();

  for(unsigned count=0; l_it!=left.operands().end(); 
      ++l_it, ++r_it, ++count)
  {
    if(paths.size()!=0)
    {
      const graph_based_interpolatort::patht &path=paths[count];

      graph_interpolantt partial;
      disequality_interpolator.find_chains(path, threshold, 
                                           callback, partial);

      interpolant.chains.splice(interpolant.chains.end(), partial.chains);
    }
    else
      assert(*l_it==*r_it);
  }

  interpolant.lift_chains(fact, threshold);
  
  return true;
}

/*******************************************************************\

Function: constant_propagationt::add_constant

  Inputs: 

 Outputs: 

 Purpose: Add constants to the constant_pool. 
          Returns false if the constant was successfully added
          to one of the pools, and true if it was not a number
          (i.e., a type that cannot be ordered)

\*******************************************************************/
bool constant_propagationt::add_constant(
  const exprt &expr, unsigned number)
{
  assert(expr.is_constant());
  
  if (!is_number(expr.type()))
    return true;
    
  constant_propagationt::typed_constant_poolt &pool=
    constant_pool[expr.type()];

  pool[to_constant_expr(expr)]=number;

  return false;
}

/*******************************************************************\

Function: constant_propagationt::add_fact

  Inputs: 

 Outputs: 

 Purpose: Function to report new facts to the propagator

\*******************************************************************/
bool constant_propagationt::add_fact(const graph_factt& fact)
{
  if(expression_pool.is_constant(fact.n))
    add_constant(expression_pool[fact.n], fact.n);
  add_subterms(fact.n);

  if(expression_pool.is_constant(fact.m))
    add_constant(expression_pool[fact.m], fact.m);
  add_subterms(fact.m);

  return true;
}

/*******************************************************************\

Function: constant_propagationt::add_subterms

  Inputs: 

 Outputs: 

 Purpose: 

\*******************************************************************/
void constant_propagationt::add_subterms(unsigned node)
{
  /* add sub-term closed pool of expressions */
  colour_ranget range;
  expression_pool.get_colour(node, range);
  
  term_pool.insert(node);
  
  // make a copy, since expression_pool may change
  const exprt expr=expression_pool[node];

  forall_operands(it, expr)
  {
    const exprt &sub=*it;
    unsigned index=expression_pool.number(sub, range);
    add_subterms(index);
  }
}

/*******************************************************************\

Function: constant_propagationt::simplify_to_constant

  Inputs: 

 Outputs: 

 Purpose: Tries to simplify an expression to a constant.
          Returns false in case of success, true otherwise.

\*******************************************************************/
bool constant_propagationt::simplify_to_constant(exprt &term)
{
  simplify(term, expression_pool.ns);
  if(term.is_constant())
    return false;

  if(term.id()==ID_typecast && term.op0().is_constant())
  {
    return simplify_typecast_to_constant(term);
  }

  return true;
}

/*******************************************************************\

Function: constant_propagationt::simplify_typecast_to_constant

  Inputs: 

 Outputs: 

 Purpose: Tries to simplify a typecast constant to a constant.
          Returns false in case of success, true otherwise.

\*******************************************************************/
bool constant_propagationt::simplify_typecast_to_constant(exprt &term)
{
  const typet &ctype=term.op0().type();
  
  if(term.type().id()==ID_pointer && 
     simplify_exprt::is_bitvector_type(ctype))
  {
    mp_integer value=0;
    if(term.op0().get(ID_value)!=ID_NULL)
      value=binary2integer(id2string(term.op0().get(ID_value)), 
                           (ctype.id()==ID_signedbv));
    
    if(value==0) // eliminate typecasts from NULL
    {
      exprt null=term.op0();
      null.type()=term.type();
      null.set(ID_value, ID_NULL);
      term.swap(null);
      return false;
    }
  }
  else if(simplify_exprt::is_bitvector_type(term.type()))
  {
    if(term.op0().get(ID_value)==ID_NULL)
    {
      term=from_integer(0, term.type());
      return false;
    }
    else
    {
      mp_integer value=
        binary2integer(id2string(term.op0().get(ID_value)), 
                       (ctype.id()==ID_signedbv));
      if(value==0)
      {
        term=from_integer(0, term.type());
        return false;
      }
    }
  }
  
  return true;
}

/*******************************************************************\

Function: constant_propagationt::infer

  Inputs: 

 Outputs: 

 Purpose: Adds the inferred equalities and inequalities. 
          Always returns true (i.e., never infers a contradiction)

\*******************************************************************/
bool constant_propagationt::infer(graph_interpolator_callbackt& callback)
{
  // perform constant propagation
  for(std::set<unsigned>::const_iterator t_it=term_pool.begin();
      t_it!=term_pool.end(); ++t_it)
  {
    unsigned unprocessed=*t_it;

    exprt expr=expression_pool[unprocessed];
    if(expr.is_constant())
      continue;

    colour_ranget range;
    bool coloured=!expression_pool.get_colour(unprocessed, range);
    assert(coloured);
   
    Forall_operands(e_it, expr)
    {
      if(e_it->is_constant())
        continue;

      unsigned representative;
      unsigned node=expression_pool.number(*e_it, range);

      if(!get_constant_info(node, representative))
      {
        *e_it=expression_pool[representative];
      }
    }

    unsigned index=expression_pool.number(expr, range);
    simplify_to_constant(expr);
    unsigned simplified=expression_pool.number(expr, range);
    
    if(unprocessed!=index && 
       (expr.is_constant() || term_pool.find(simplified)!=term_pool.end()))
    {
      // add new equalities
      graph_factt fact;
      fact.derivation=wordlevel_factt::CONSTANT_PROPAGATION;
      fact.rel=graph_factt::EQUAL;
      fact.n=unprocessed; fact.m=index;
      fact.partition=range.first;

      congruences.add_fact(fact); // remember the justification
      callback.add_fact(fact);
      
      if(simplified!=index)
      {
        fact.derivation=wordlevel_factt::THEORY_FACT;
        fact.n=index; fact.m=simplified;
        callback.add_fact(fact);
      }
    }
  }

  infer_inequalities(callback);
  infer_disequalities(callback);

  return true;
}

/*******************************************************************\

Function: constant_propagationt::infer_inequalities

  Inputs: 

 Outputs: 

 Purpose: Adds the inferred inequality chains
          for comparable constants.

\*******************************************************************/
void constant_propagationt::infer_inequalities(
  graph_interpolator_callbackt& callback)
{
  std::list<graph_factt> new_facts;

  for (constant_poolt::const_iterator p_it=constant_pool.begin();
       p_it!=constant_pool.end(); p_it++)
  {
    const typed_constant_poolt &pool=p_it->second;
    
    for (typed_constant_poolt::const_iterator c_it=pool.begin();
         c_it!=pool.end(); c_it++)
    {
      typed_constant_poolt::const_iterator next=c_it; 
      next++;
      
      if (next!=pool.end()) // generate an axiom c1<c2
      {
        graph_factt fact;
        fact.rel=graph_factt::GREATER_THAN;
        fact.n=next->second;
        fact.m=c_it->second;
        fact.derivation=wordlevel_factt::THEORY_FACT;
        fact.partition=0;
        // we can't call add_fact here because this might invalidate p_it
        new_facts.push_back(fact);
      }
    }
  }

  for(std::list<graph_factt>::const_iterator n_it=new_facts.begin();
      n_it!=new_facts.end(); ++n_it)
    callback.add_fact(*n_it);
}

/*******************************************************************\

Function: constant_propagationt::infer_disequalities

  Inputs: 

 Outputs: 

 Purpose: 

\*******************************************************************/
void constant_propagationt::infer_disequalities(
  graph_interpolator_callbackt& callback)
{
  // process pending disequalities
  for(; !inferred_disequalities.empty(); inferred_disequalities.pop())
  {
    graph_factt &fact=inferred_disequalities.top();
    assert(fact.n!=fact.m && fact.rel==graph_factt::NOT_EQUAL);
    callback.add_fact(fact);
  }  
}


/*******************************************************************\

Function: constant_propagationt::ordert::operator()

  Inputs: Two expressions representing constant numbers

 Outputs: 

 Purpose: Imposes an order between two constant numbers

\*******************************************************************/
bool constant_propagationt::ordert::operator()
  (const constant_exprt& a, const constant_exprt& b) const
{
  mp_integer va, vb;
  rationalt ra, rb;

  if ((a.type().id()=="fixedbv")||(b.type().id()=="fixedbv"))
  {
    fixedbvt fa(a); fixedbvt fb(b);
    return (fa<fb);
  }
  else if ((a.type().id()=="floatbv")||((a.type().id()=="floatbv")))
  {
    ieee_floatt fa(a); ieee_floatt fb(b);
    return (fa<fb);
  }
  else if (!to_integer(a, va) && !to_integer(b, vb))
  {
    return (va<vb);
  }
  else if (!to_rational(a, ra) && !to_rational(b, rb))
  {
    return (ra<rb);
  }
  else
    assert(false); // comparison failed!
}

/*******************************************************************\

Function: dynamic_object_poolt::add_class

  Inputs: 

 Outputs: 

 Purpose: Checks whether a new term is a valid (non-null) object.

\*******************************************************************/
void dynamic_object_poolt::add_class(unsigned index)
{
  const exprt expr=expression_pool[index];
  if(expr.type().id()!=ID_pointer)
    return;

  process_subterms(index, expr);
}

/*******************************************************************\

Function: dynamic_object_poolt::is_valid_object

  Inputs: 

 Outputs: 

 Purpose: 

\*******************************************************************/
bool dynamic_object_poolt::is_valid_object(const exprt& expr)
{
  if(expr.id()==ID_symbol)
    return true;

  if(expr.id()==ID_index)
  {
    const index_exprt &index_expr=to_index_expr(expr);
    const exprt &array=index_expr.array();
    if(array.id()==ID_symbol || array.id()==ID_string_constant)
      return true;
  }

  if(expr.id()==ID_member)
  {
    const member_exprt &member_expr=to_member_expr(expr);
    if(member_expr.struct_op().id()==ID_symbol)
      return true;
  }

  return false;
}

/*******************************************************************\

Function: dynamic_object_poolt::add_object_to_pool

  Inputs: 

 Outputs: 

 Purpose: Adds an object with a unique address to the object
          pool and adds an inequality if there's another object
          with a different address. We can safely assume that
          the terms are in the same partition, since they're 
          actually representing constants!

\*******************************************************************/
void dynamic_object_poolt::add_to_object_pool(
  unsigned index, const exprt& expr)
{
  std::set<unsigned> &typed_pool=object_pool[expr.type()];

  colour_ranget range, range_other;       
  if(expression_pool.get_colour(index, range))
    return;

  for(std::set<unsigned>::const_iterator o_it=typed_pool.begin();
      o_it!=typed_pool.end(); ++o_it)
  {
    unsigned other=*o_it;
    
    pending.push_back(graph_factt());
    graph_factt &fact=pending.back();
    fact.derivation=wordlevel_factt::THEORY_FACT;
    fact.rel=graph_factt::NOT_EQUAL;
    fact.partition=range.second;
    fact.n=index;
    fact.m=other;
  }
  
  typed_pool.insert(index);
}

/*******************************************************************\

Function: dynamic_object_poolt::process_subterms

  Inputs: 

 Outputs: 

 Purpose: Processes typecasts

\*******************************************************************/
void dynamic_object_poolt::process_subterms(
  unsigned index, const exprt& expr)
{
  unsigned representative=
    disequality_interpolator.get_representative(index);

  if(valid_objects.find(representative)!=valid_objects.end() ||
     (expr.id()!=ID_address_of && expr.id()!=ID_typecast))
    return;

  colour_ranget range;
  expression_pool.get_colour(index, range);

  constant_exprt null(expr.type());
  null.set(ID_value, ID_NULL);

  if(expr.id()==ID_address_of && is_valid_object(expr.op0()))
  {
    add_to_object_pool(index, expr);
    
    valid_objects[representative]=index;

    pending.push_back(graph_factt());
    graph_factt &fact=pending.back();
    fact.derivation=wordlevel_factt::THEORY_FACT;
    fact.rel=graph_factt::NOT_EQUAL;
    fact.partition=range.second;
    fact.n=index;
    fact.m=expression_pool.number(null, range);

    // now propagate
    process_uselist(representative);
  }
  else if(expr.id()==ID_typecast)
  {
    const exprt &operand=expr.op0();
    unsigned op_index=expression_pool.number(operand, range);

    // recursively process sub-terms
    process_subterms(op_index, operand);

    unsigned op_representative=
      disequality_interpolator.get_representative(op_index);
    valid_objectst::const_iterator v_it=valid_objects.find(op_representative);

    if(v_it!=valid_objects.end())
    {
      // typecast must also be non-null!
      valid_objects[representative]=index;
      
      pending.push_back(graph_factt());
      graph_factt &fact=pending.back();
      fact.derivation=wordlevel_factt::DYNAMIC_OBJECT_POOL;
      fact.rel=graph_factt::NOT_EQUAL;
      fact.partition=range.second;
      fact.n=index;
      fact.m=expression_pool.number(null, range);

      // remember the justification
      congruences.add_fact(fact, op_index, v_it->second);

      // now propagate
      process_uselist(representative);
    }
    else 
    {
      // remember this for later
      use_list[op_representative].push_back(index);
    }
  }
}

/*******************************************************************\

Function: dynamic_object_poolt::process_uselist

  Inputs: 

 Outputs: 

 Purpose: Processes all the elements in the uselist of a non-null
          element.

\*******************************************************************/
void dynamic_object_poolt::process_uselist(unsigned nonnull)
{
  std::list<unsigned> &used=use_list[nonnull];

  for(std::list<unsigned>::const_iterator u_it=used.begin();
      u_it!=used.end(); ++u_it)
  {
    const unsigned index=*u_it;
    unsigned representative=
      disequality_interpolator.get_representative(index);

    if(valid_objects.find(representative)==valid_objects.end())
    {
      valid_objects[representative]=index;

      const exprt expr=expression_pool[index];
      assert(expr.id()==ID_typecast);
      const exprt &operand=expr.op0();
      
      colour_ranget range;
      expression_pool.get_colour(index, range);

      constant_exprt null(expr.type());
      null.set(ID_value, ID_NULL);
      
      pending.push_back(graph_factt());
      graph_factt &fact=pending.back();
      fact.derivation=wordlevel_factt::DYNAMIC_OBJECT_POOL;
      fact.rel=graph_factt::NOT_EQUAL;
      fact.partition=range.second;
      fact.n=index;
      fact.m=expression_pool.number(null, range);
   
      // remember the justification
      unsigned sub_index=expression_pool.number(operand, range);
      congruences.add_fact(fact, sub_index, valid_objects[nonnull]);

      process_uselist(representative);
    }
  }

  // we've processed all elements in the uselist
  used.clear(); 
}

/*******************************************************************\

Function: dynamic_object_poolt::merge

  Inputs: 

 Outputs: 

 Purpose: Merges two equivalence classes and infers 
          new valid objects from the use_list if possible

\*******************************************************************/
void dynamic_object_poolt::merge(unsigned oldrep, unsigned newrep)
{
  valid_objectst::const_iterator v_it=valid_objects.find(newrep);
  if(v_it==valid_objects.end())
    v_it=valid_objects.find(oldrep);

  if(v_it==valid_objects.end())
    return;

  // merge the representatives
  if(v_it->first==oldrep) // there's no non-null object for newrep 
    valid_objects[newrep]=valid_objects[oldrep];

  // merge the uselists
  std::list<unsigned> &used=use_list[newrep];
  used.splice(used.end(), use_list[oldrep]);

  process_uselist(newrep);
}

/*******************************************************************\

Function: dynamic_object_poolt::infer

  Inputs: 

 Outputs: 

 Purpose: Adds the newly inferred inequalities. Always returns true

\*******************************************************************/
bool dynamic_object_poolt::infer(graph_interpolator_callbackt& callback)
{
  // process pending inequalities
  for(graph_fact_listt::const_iterator p_it=pending.begin();
      p_it!=pending.end(); ++p_it)
  {
    const graph_factt &fact=*p_it;
    callback.add_fact(fact);
  }

  return true;
}

/*******************************************************************\

Function: dynamic_object_poolt::get_interpolant

  Inputs: 

 Outputs: 

 Purpose: Returns a partial interpolant for a fact inferred by
          means of propagation of non-null dynamic objects

\*******************************************************************/
bool dynamic_object_poolt::get_interpolant(
  const graph_factt& fact, 
  wordlevel_factt::partitiont threshold,
  graph_interpolator_callbackt& callback, 
  graph_interpolantt& interpolant)
{
  assert(fact.derivation==wordlevel_factt::DYNAMIC_OBJECT_POOL);

  const congruencest::pathst &paths=congruences.get_justification(fact);
  assert(paths.size()!=0);
  const graph_based_interpolatort::patht &path=paths[0];

  graph_interpolantt partial;
  disequality_interpolator.find_chains(path, threshold, 
                                       callback, partial);

  if(partial.chains.size()!=0)
  {
    // now extend the chain with the !=NULL inequality!
    const exprt left=expression_pool[fact.n];
    const exprt right=expression_pool[fact.m];
    
    if(left.is_constant() && left.get(ID_value)==ID_NULL)
    {
      graph_interpolantt::chaint &chain=partial.chains.front();
      assert(chain.fact.rel==graph_factt::EQUAL);
      
#ifdef DEBUG
      unsigned rep=disequality_interpolator.get_representative(chain.fact.n);
      assert(valid_objects[rep]=chain.fact.n);
#endif
      
      chain.fact.rel=graph_factt::NOT_EQUAL;
      exprt object=expression_pool[chain.fact.n];
      constant_exprt null(object.type());
      null.set(ID_value, ID_NULL);
      chain.fact.n=expression_pool.number(null);
    }
    else
    {
      assert(right.is_constant() && right.get(ID_value)==ID_NULL);
      graph_interpolantt::chaint &chain=partial.chains.back();
      assert(chain.fact.rel==graph_factt::EQUAL);
      
#ifdef DEBUG
      unsigned rep=disequality_interpolator.get_representative(chain.fact.m);
      assert(valid_objects[rep]=chain.fact.m);
#endif
      
      chain.fact.rel=graph_factt::NOT_EQUAL;
      exprt object=expression_pool[chain.fact.m];
      constant_exprt null(object.type());
      null.set(ID_value, ID_NULL);
      chain.fact.m=expression_pool.number(null);
    }
  }
  
  interpolant.chains.splice(interpolant.chains.end(), partial.chains);
  interpolant.lift_chains(fact, threshold);  

  return true;
}


/*******************************************************************\

Function: array_propagationt::add_fact

  Inputs: 

 Outputs: 

 Purpose: Scans a fact for array accesses and adds them to the
          appropriate list

\*******************************************************************/
void array_propagationt::add_fact(const graph_factt& fact)
{
  add_subterms(expression_pool[fact.n], fact.partition);
  add_subterms(expression_pool[fact.m], fact.partition);

  // now try to detect assignments to arrays
  if(fact.derivation!=wordlevel_factt::TOPLEVEL_FACT ||
     fact.rel!=graph_factt::EQUAL)
    return;

  const exprt left=expression_pool[fact.n];
  const exprt right=expression_pool[fact.m];

  exprt with, target;

  if(left.id()==ID_with && left.op0().type().id()==ID_array)
  {
    with=left; target=right;
  }
  else if(right.id()==ID_with && right.op0().type().id()==ID_array)
  {
    with=right; target=left;
  }
  else
    return;

  assert(target.type().id()==ID_array);
  assert(with.operands().size()==3);

  // remember assignment to array
  array_updatet &update=array_updates[target];
  update.with=with;
  update.fact=fact;
}

/*******************************************************************\

Function: array_propagationt::add_fact

  Inputs: 

 Outputs: 

 Purpose: Scans a fact for array accesses and adds them to the
          appropriate list

\*******************************************************************/
void array_propagationt::add_subterms(
  const exprt& term, wordlevel_factt::partitiont colour)
{
  if(term.id()==ID_index && term.operands().size()==2)
  {
    const index_exprt &index_expr=to_index_expr(term);
    const exprt &array=index_expr.array();
    const exprt &index=index_expr.index();

    unsigned array_node=expression_pool.number(array, colour);
    unsigned index_node=expression_pool.number(index, colour);

    array_accesses.insert(
      std::pair<unsigned,unsigned>(array_node, index_node));
  }

  forall_operands(it, term)
    add_subterms(*it, colour);
}


/*******************************************************************\

Function: array_propagationt::infer

  Inputs: 

 Outputs: 

 Purpose: Adds the inferred equalities for arrays and structs.
          Always returns true (i.e., never infers a contradiction)

\*******************************************************************/
bool array_propagationt::infer(
  graph_interpolator_callbackt& callback)
{
  graph_factt fact;
  fact.rel=graph_factt::EQUAL;

  std::list<graph_factt> new_facts;

  for(array_updatest::const_iterator u_it=array_updates.begin();
      u_it!=array_updates.end(); ++u_it)
  {
    const exprt& array=u_it->first;
    const array_updatet &update=u_it->second;

    unsigned updated_index=expression_pool.number(update.with.op1());
    unsigned array_node=expression_pool.number(array);

    // try to find a representative constant for the update index
    unsigned updated_index_constant;

    if(expression_pool.is_constant(updated_index))
      updated_index_constant=updated_index;
    else 
    {
      if(constant_propagation.get_constant_info(updated_index, 
                                                updated_index_constant))
      {
        continue;
      }
    }

    std::pair<array_accessest::iterator, array_accessest::iterator> 
      range=array_accesses.equal_range(array_node);

    // add a fact a'[i]=v derived from a'=a[with i=v]
    fact.derivation=wordlevel_factt::TOPLEVEL_FACT;
    fact.partition=update.fact.partition;

    index_exprt target(array, expression_pool[updated_index]);
    fact.n=expression_pool.number(target, fact.partition);
    fact.m=expression_pool.number(update.with.op2(), fact.partition);

    new_facts.push_back(fact);

    // iterate over all array accesses
    for(array_accessest::const_iterator a_it=range.first;
        a_it!=range.second; ++a_it)
    {
      const unsigned accessed_index=a_it->second;
      unsigned accessed_index_constant;

      // try to find a representative constant for the access index
      if(expression_pool.is_constant(accessed_index))
        accessed_index_constant=accessed_index;
      else
      {
        if(constant_propagation.get_constant_info(accessed_index, 
                                                  accessed_index_constant))
          continue;
      }

      // check if we need to propagate the array content
      switch(expression_pool.compare_constants(accessed_index_constant,
                                               updated_index_constant))
      {
      case decision_proceduret::D_UNSATISFIABLE: 
        {
          exprt index=expression_pool[accessed_index_constant]; 
          index_exprt left(array, index);
          fact.n=expression_pool.number(left, fact.partition);

          index_exprt right(update.with.op0(), index);
          fact.m=expression_pool.number(right, fact.partition);
          
          if(updated_index==updated_index_constant)
          {
            // updated_index is a constant
            fact.derivation=wordlevel_factt::TOPLEVEL_FACT;
          }
          else
          {
            // updated_index_constant!=accessed_index_constant and
            // updated_index==update_index_constant implies the fact
            fact.derivation=wordlevel_factt::ARRAY_INTERPOLATOR;
            // remember the justifying equality
            congruences.add_fact(fact, updated_index, updated_index_constant); 
          }
        }
        break;
      default:
        continue;
      }

      // can't call callback here, since it might invalidate u_it
      new_facts.push_back(fact);
    }
  }

  for(std::list<graph_factt>::const_iterator n_it=new_facts.begin();
      n_it!=new_facts.end(); ++n_it)
    callback.add_fact(*n_it);

  return true;
}

/*******************************************************************\

Function: array_propagationt::get_interpolant

  Inputs: 

 Outputs: 

 Purpose: Returns a partial interpolant for a fact inferred by
          means of propagation for data structures.

\*******************************************************************/
bool array_propagationt::get_interpolant(
  const graph_factt& fact, 
  wordlevel_factt::partitiont threshold,
  graph_interpolator_callbackt& callback, 
  graph_interpolantt& interpolant)
{
  assert(fact.derivation==wordlevel_factt::ARRAY_INTERPOLATOR);

  const congruencest::pathst &paths=congruences.get_justification(fact);
  assert(paths.size()!=0);
  const graph_based_interpolatort::patht &path=paths[0];

  graph_interpolantt partial;
  disequality_interpolator.find_chains(path, threshold, 
                                       callback, partial);

  interpolant.chains.splice(interpolant.chains.end(), partial.chains);
  interpolant.lift_chains(fact, threshold);  

  return true;
}

/*******************************************************************\

Function: arithmetic_interpolatort::add_fact

  Inputs: 

 Outputs: 

 Purpose: Applies a number of simple arithmetic rewriting rules
          to the provided fact. This is very restricted and only
          applies to toplevel facts (since we'd otherwise run
          into trouble with colouring the inferred facts).

\*******************************************************************/
void arithmetic_interpolatort::add_fact(const graph_factt& fact)
{
  if(fact.derivation!=wordlevel_factt::TOPLEVEL_FACT || inconsistent)
    return;

  switch(fact.rel)
  {
  case graph_factt::GREATER_THAN:
    postponed_facts[(unsigned)fact.rel].push_back(fact);
    break;
  default:
    break;
  }
}

/*******************************************************************\

Function: arithmetic_interpolatort::process_greater_than

  Inputs: 

 Outputs: 

 Purpose: Implements the following rules:
          (unsigned)a<0 |- false
          (unsigned)a<1 |- a=0

\*******************************************************************/
void arithmetic_interpolatort::process_greater_than(
  const graph_factt& fact, graph_interpolator_callbackt& callback)
{
  unsigned constant;
  
  if(expression_pool.is_constant(fact.n))
    constant=fact.n;
  else if(constant_propagation.get_constant_info(fact.n, constant))
    return;
    
  const exprt term=expression_pool[fact.m];
  if(term.type().id()==ID_unsignedbv)
  {
    const exprt const_term=expression_pool[constant];
    
    if(const_term.is_zero())
    {
      inconsistent=true;
      contradiction.n=fact.n;
      contradiction.m=fact.n;
      contradiction.rel=graph_factt::GREATER_THAN;
      contradiction.derivation=wordlevel_factt::ARITHMETIC_INTERPOLATOR;
      contradiction.partition=fact.partition;
      premises[contradiction]=fact;
      derivation_types[contradiction]=EQUALITY_DERIVATION;
      congruences.add_fact(contradiction, fact.n, constant);
    }
    else if(const_term.is_one())
    {
      graph_factt new_fact;
      new_fact.n=fact.m;
      const exprt zero=from_integer(0, term.type());
      new_fact.m=expression_pool.number(zero, fact.partition);
      new_fact.rel=graph_factt::EQUAL;
      new_fact.derivation=wordlevel_factt::ARITHMETIC_INTERPOLATOR;
      new_fact.partition=fact.partition;
      premises[new_fact]=fact;
      derivation_types[new_fact]=EQUALITY_DERIVATION;
      congruences.add_fact(new_fact, fact.n, constant);
      callback.add_fact(new_fact);
    }
  }
}

/*******************************************************************\

Function: arithmetic_interpolatort::infer

  Inputs: 

 Outputs: 

 Purpose: Returns false if an inconsistency can be inferred

\*******************************************************************/
bool arithmetic_interpolatort::infer(
  graph_interpolator_callbackt& callback)
{
  graph_fact_listt::const_iterator f_it;

  for(f_it=postponed_facts[graph_factt::GREATER_THAN].begin();
      f_it!=postponed_facts[graph_factt::GREATER_THAN].end(); 
      ++f_it)
  {
    process_greater_than(*f_it, callback);
  }

  postponed_facts.clear();
        
  if(inconsistent)
  {
    callback.report_contradiction(contradiction);
    return false;
  }
    
  return true;
}

/*******************************************************************\

Function: arithmetic_interpolatort::get_interpolant

  Inputs: 

 Outputs: 

 Purpose: Returns an interpolant for the given fact. Returns false
          if this fact is the contradictive one.

\*******************************************************************/
bool arithmetic_interpolatort::get_interpolant(
  const graph_factt& fact,
  wordlevel_factt::partitiont threshold,
  graph_interpolator_callbackt& callback,
  graph_interpolantt& interpolant)
{
  assert(fact.derivation==wordlevel_factt::ARITHMETIC_INTERPOLATOR);
  
  graph_factt actual_fact=fact;
  
  premisest::const_iterator p_it=premises.find(fact);
  if(p_it==premises.end())
  {
    assert(fact.rel==graph_factt::EQUAL);
    actual_fact.n=fact.m;
    actual_fact.m=fact.n;
    p_it=premises.find(actual_fact);
    assert(p_it!=premises.end());
  }

  const graph_factt &premise=p_it->second;

  if(premise.derivation!=wordlevel_factt::TOPLEVEL_FACT &&
     premise.derivation!=wordlevel_factt::THEORY_FACT)
  {
    callback.get_interpolant(premise, threshold, interpolant);      
  }
    
  const congruencest::pathst &paths=congruences.get_justification(actual_fact);
  for(unsigned position=0; position<paths.size(); position++)
  {
    graph_interpolantt partial;
    const graph_based_interpolatort::patht &path=paths[position];
    
    disequality_interpolator.find_chains(path, threshold, 
                                         callback, partial);
    interpolant.chains.splice
      (interpolant.chains.end(), partial.chains);
  }
  
  interpolant.lift_chains(contradiction, threshold);
  
  if(actual_fact==contradiction)
    return false;  
  return true;
}


/*******************************************************************\

Function: expression_poolt::expression_poolt

  Inputs: 

 Outputs: 

 Purpose: Constructor for the expression pool

\*******************************************************************/
expression_poolt::expression_poolt(const namespacet &_ns): 
  ns(_ns), max_partition(0)
{
  // initialise numbering with some standard expressions
  true_num=number(true_exprt(), 0);
  false_num=number(false_exprt(), 0);
}

/*******************************************************************\

Function: expression_poolt::massage

  Inputs: An expression 

 Outputs: 

 Purpose: Tries to eliminate glitches and artefacts from 
          an expression that may lead the expression-pool
          to treat two equal terms as different

\*******************************************************************/
void expression_poolt::massage(exprt& expression)
{
  typet &type=expression.type();
  
  if(type.has_subtype() && type.subtype().id()=="")
    type.remove_subtype();
} 


/*******************************************************************\

Function: expression_poolt::number

  Inputs: An expression. 

 Outputs: 

 Purpose: Returns a unique number for an expression.

\*******************************************************************/
unsigned expression_poolt::number(const exprt &expression)
{
  exprt massaged=expression; massage(massaged);
  unsigned n=expression_numbers.number(massaged);

#ifdef DEBUG
  std::cout << n << " |-> " << from_expr(ns, "", massaged) << std::endl;
#endif

  return n;
}

/*******************************************************************\

Function: expression_poolt::number

  Inputs: An expression and a partition number 

 Outputs: 

 Purpose: Returns a unique number for an expression.

\*******************************************************************/
unsigned expression_poolt::number(
  const exprt &expression, wordlevel_factt::partitiont colour)
{
  unsigned n=number(expression);
  add_colour(n, colour);

#ifdef DEBUG
  std:: cout << "      with colour " << colour << std::endl;
#endif

  return n;
}

/*******************************************************************\

Function: expression_poolt::number

  Inputs: An expression and a colour range

 Outputs: 

 Purpose: Returns a unique number for an expression.

\*******************************************************************/
unsigned expression_poolt::number(
  const exprt &expression, const colour_ranget &range)
{
  unsigned n=number(expression);
  add_colour(n, range);

#ifdef DEBUG
  std::cout << "      with range [" 
            << range.first << "," << range.second 
            << "]" << std::endl;
#endif

  return n;
}

/*******************************************************************\

Function: expression_poolt::operator[]

  Inputs: A number identifying an expression in the pool 

 Outputs: 

 Purpose: Returns the expression corresponding to the given number.

\*******************************************************************/
const exprt& expression_poolt::operator[](unsigned number) const
{
  return expression_numbers[number];
}

/*******************************************************************\

Function: expression_poolt::add_colour

  Inputs: A node id and a potential colour for that node

 Outputs: 

 Purpose: 

\*******************************************************************/
void expression_poolt::add_colour(unsigned n, unsigned colour)
{
  if(n>=colouring.size())
    colouring.resize(n+1, std::pair<unsigned,unsigned>(1,0));
  
  colour_ranget &range=colouring[n];

  if(range.first>range.second)
  {
    range.first=colour;
    range.second=colour;
  }
  else if(colour<range.first)
  {
    range.first=colour;
  }
  else if(colour>range.second)
  {
    range.second=colour;
  }
}

/*******************************************************************\

Function: expression_poolt::add_colour

  Inputs: A node id and a colour range for that node

 Outputs: 

 Purpose: 

\*******************************************************************/
void expression_poolt::add_colour(unsigned n, const colour_ranget& range)
{
  if(range.first<=range.second) // is this a valid colour range?
  {
    add_colour(n, range.first);
    add_colour(n, range.second);
  }
}

/*******************************************************************\

Function: expression_poolt::inherit_colour

  Inputs: A source node id and a target node id

 Outputs: 

 Purpose: 

\*******************************************************************/
void expression_poolt::inherit_colour(unsigned n, unsigned m)
{
  colour_ranget range;

  if(!get_colour(n, range))
    add_colour(m, range);
}

/*******************************************************************\

Function: expression_poolt::set_colour

  Inputs: A node id and a fixed colour for that node

 Outputs: 

 Purpose: Set the colour of a node to a fixed value

\*******************************************************************/
void expression_poolt::set_colour(unsigned n, unsigned colour)
{
  if(n>=colouring.size())
    colouring.resize(n+1, std::pair<unsigned,unsigned>(1,0));
  
  colour_ranget &range=colouring[n];

  range.first=colour;
  range.second=colour;
}

/*******************************************************************\

Function: expression_poolt::get_colour

  Inputs: A node id "n"

 Outputs: Returns false and a range if the colour range for n is 
          valid, true otherwise

 Purpose: 

\*******************************************************************/
bool expression_poolt::get_colour(unsigned n, colour_ranget& range) const
{
  if(n>=colouring.size())
    return true;

  range=colouring[n];
  
  if(range.first>range.second)
    return true;

  return false;
}

/*******************************************************************\

Function: expression_poolt::is_colourable

  Inputs: A node id "n" and a colour

 Outputs: Returns true if "n" can be coloured with the given colour

 Purpose: 

\*******************************************************************/
bool expression_poolt::is_colourable(unsigned n, unsigned colour) const
{
  if(n>=colouring.size())
    return false;

  const colour_ranget &range=colouring[n];
  
  if(range.first<=colour && colour<=range.second)
    return true;

  return false;
}

/*******************************************************************\

Function: expression_poolt::compare

  Inputs: Two constant expression indices

 Outputs: 

 Purpose: Returns 
            D_TAUTOLOGY     if the two constants are the same
            D_UNSATISABLE if the two constants are different
            D_SATISFABLE   if it can't be determined
          Performs typecasting if possible.

\*******************************************************************/
decision_proceduret::resultt
expression_poolt::compare_constants(unsigned a, unsigned b)
{
  if(a==b)
    return decision_proceduret::D_SATISFIABLE;

  mp_integer left_value;
  mp_integer right_value;

  exprt left=(*this)[a];
  exprt right=(*this)[b];

  simplify(left, ns);
  simplify(right, ns);
  
  if(left.type().id()=="bool" && right.type().id()=="bool")
  {
    if((left.is_true() && right.is_false()) ||
       (left.is_false() && right.is_true()))
      return decision_proceduret::D_UNSATISFIABLE;
    else
      return decision_proceduret::D_SATISFIABLE;
  }

  if(to_integer(left, left_value) || to_integer(right, right_value))
    return decision_proceduret::D_SATISFIABLE;
  
  if(left_value==right_value)
    return decision_proceduret::D_SATISFIABLE;
  else
    return decision_proceduret::D_UNSATISFIABLE;
}

/*******************************************************************\

Function: expression_poolt::size()

  Inputs: 

 Outputs: 

 Purpose: Returns the number of expressions in the pool

\*******************************************************************/
unsigned expression_poolt::size() const
{
  return expression_numbers.size();
}

/*******************************************************************\

Function: expression_poolt::to_string

  Inputs: 

 Outputs: 

 Purpose: Pretty prints an expression (using the default namespace).
          Index must be a valid index!

\*******************************************************************/
std::string expression_poolt::to_string(unsigned node)
{
  return from_expr(ns, "", (*this)[node]);
}

/*******************************************************************\

Function: graph_axiomst::graph_axiomst

  Inputs: 

 Outputs: 

 Purpose: Constructor

\*******************************************************************/
graph_axiomst::graph_axiomst
(expression_poolt &pool):
  expression_pool(pool),
  GRAPH_RULE_CONSTRUCTORS(expression_pool)
{ 
}

/*******************************************************************\

Function: graph_axiomst::add_fact

  Inputs: 

 Outputs: 

 Purpose: 

\*******************************************************************/
void graph_axiomst::add_fact(const graph_factt& fact)
{
  rewrite_term(fact.n, fact.partition);
  rewrite_term(fact.m, fact.partition);
  rewrite_fact(fact);

  unsigned max=std::max(fact.n, fact.m);
  if(max>processed.size())
    processed.resize(max+1, false);

  processed[fact.n]=true;
  processed[fact.m]=true;
}

/*******************************************************************\

Function: graph_axiomst::process_term

  Inputs: A term that occured in the facts

 Outputs: 

 Purpose: Applies all rules to a given term

\*******************************************************************/
void graph_axiomst::rewrite_term(
  unsigned index, wordlevel_factt::partitiont partition)
{
  GRAPH_REWRITE_TERMS;
}

/*******************************************************************\

Function: graph_axiomst::process_fact

  Inputs: 

 Outputs: 

 Purpose: Applies all rules to a given fact

\*******************************************************************/
void graph_axiomst::rewrite_fact(const graph_factt& fact)
{
  GRAPH_REWRITE_FACTS;
}

/*******************************************************************\

Function: graph_axiomst::add_axiom

  Inputs: The axiom (a graph fact) and a trigger

 Outputs: 

 Purpose: The axiom will be instantiated if the trigger expression
          occurs.

\*******************************************************************/
void graph_axiomst::add_axiom(
  const graph_factt &fact, unsigned trigger)
{
  axiom_pool.push_back(
    std::pair<graph_factt, unsigned>(fact, trigger));
}

/*******************************************************************\

Function: graph_axiomst::infer

  Inputs: A graph callback object

 Outputs: 

 Purpose: Instantiates rules if the respective trigger terms have
          been encountered

\*******************************************************************/
void graph_axiomst::infer(graph_interpolator_callbackt& callback)
{
  for (axiom_poolt::iterator a_it=axiom_pool.begin();
       a_it!=axiom_pool.end();)
  {
    const graph_factt &fact=a_it->first;
    unsigned trigger=a_it->second;
    
    axiom_poolt::iterator c_it=a_it;
    ++a_it;

    if((processed.size()>trigger && processed[trigger]) || (trigger==0))
    {
      callback.add_fact(fact);
      axiom_pool.erase(c_it); // now we don't need it anymore
    }
    else
    {
#ifdef DEBUG
      std::cout << " Not instantiating " << fact.n 
                << " " << fact.relation_to_string(fact.rel) << " "
                << fact.m << " because " << trigger << " is not there\n";
#endif
    }
  }
}

/*******************************************************************\

Function: transitivity_interpolatort::infer

  Inputs: 

 Purpose: Returns D_UNSATISFIABLE if a contradiction can be inferred,
          and D_ERROR otherwise

\*******************************************************************/
decision_proceduret::resultt transitivity_interpolatort::infer()
{
  if(inconsistent)
    return decision_proceduret::D_UNSATISFIABLE;

  do {
    facts_changed=false; // updated by callback add_fact

    if(inequality_interpolator.infer(*this))
    {
      uif_interpolator.infer(*this);
      constant_propagation.infer(*this);
      array_propagation.infer(*this);
      dynamic_object_pool.infer(*this);

      graph_axioms.infer(*this);

      if(!disequality_interpolator.infer(*this))
        return decision_proceduret::D_UNSATISFIABLE;

      if(!arithmetic_interpolator.infer(*this))
        return decision_proceduret::D_UNSATISFIABLE;
    }
    else
      return decision_proceduret::D_UNSATISFIABLE;

  } while(facts_changed);

  return decision_proceduret::D_ERROR;
}


/*******************************************************************\

Function: transitivity_interpolatort::get_interpolant

  Inputs: 

 Outputs: 

 Purpose: 

\*******************************************************************/
void transitivity_interpolatort::get_interpolant
(wordlevel_factt::partitiont threshold, exprt& interpolant_expression)
{
  assert (inconsistent);

  graph_interpolantt interpolant;

  // we only need to consider interpolators that can derive a contradiction
  switch(contradiction.derivation)
  {
  case wordlevel_factt::INEQUALITY_INTERPOLATOR:
    contradiction.partition=maximal_partition; // make sure this is a B-fact
    inequality_interpolator.get_interpolant
      (contradiction, threshold, (*this), interpolant);
    break;
  case wordlevel_factt::DISEQUALITY_INTERPOLATOR:
    contradiction.partition=maximal_partition; // make sure this is a B-fact
    disequality_interpolator.get_interpolant
      (contradiction, threshold, (*this), interpolant);
    break;
  case wordlevel_factt::ARITHMETIC_INTERPOLATOR:
    arithmetic_interpolator.get_interpolant
      (contradiction, threshold, (*this), interpolant);
    break;
  case wordlevel_factt::TOPLEVEL_FACT:
  {
    // false if in A, true if in B
    if(contradiction.partition<threshold)
      interpolant_expression.make_false();
    else
      interpolant_expression.make_true();
    return;
  }
  break;
  default:
    assert(false);
  }

  assert(interpolant.chains.size()==1);

  interpolant_expression=
    interpolant.to_expression(interpolant.chains.front(), expression_pool);
}

/*******************************************************************\

Function: transitivity_interpolatort::get_interpolants

  Inputs: 

 Outputs: 

 Purpose: 

\*******************************************************************/
void transitivity_interpolatort::get_interpolants(expr_listt& expressions)
{
  for (unsigned threshold=1; threshold<=maximal_partition; threshold++)
  {
    expressions.push_back(exprt());
    get_interpolant (threshold, expressions.back());
  }
}

