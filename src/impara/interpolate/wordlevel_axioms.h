/*******************************************************************\

Module: Wordlevel rules instantiating axioms

Author: Georg Weissenbacher, georg@weissenbacher.name,
        Mark Kattenbelt, mark.kattenbelt@comlab.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_WORDLEVEL_AXIOMS_H
#define CPROVER_WORDLEVEL_AXIOMS_H

#define GRAPH_RULE_DECLARATIONS                 \
  added_constant_rulet added_constant_rule;     \
  bitseq_extract_rulet bitseq_extract_rule;     \
  bit_replication_rulet bit_replication_rule;   \
  bitvec_upcast_rulet bitvec_upcast_rule;       \
  conditional_cast_rulet cond_cast_rule;        \
  struct_with_rulet struct_with_rule;           \
  null_pointer_cast_rulet npointer_cast_rule;   \
  shift_rulet shift_rule;                       \
  bitwise_conjunction_rulet bitwise_conj_rule


#define GRAPH_RULE_CONSTRUCTORS(pool)           \
  added_constant_rule(pool),                    \
  bitseq_extract_rule(pool),                    \
  bit_replication_rule(pool),                   \
  bitvec_upcast_rule(pool),                     \
  cond_cast_rule(pool),                         \
  struct_with_rule(pool),                       \
  npointer_cast_rule(pool),                     \
  shift_rule(pool),                             \
  bitwise_conj_rule(pool)

#define GRAPH_REWRITE_TERMS                     \
  added_constant_rule.rewrite_term(index, partition, *this); \
  bitseq_extract_rule.rewrite_term(index, partition, *this); \
  bit_replication_rule.rewrite_term(index, partition, *this); \
  npointer_cast_rule.rewrite_term(index, partition, *this);  \
  shift_rule.rewrite_term(index, partition, *this);

#define GRAPH_REWRITE_FACTS                     \
  bitvec_upcast_rule.rewrite_fact(fact, *this); \
  cond_cast_rule.rewrite_fact(fact, *this);     \
  struct_with_rule.rewrite_fact(fact, *this);   \
  shift_rule.rewrite_fact(fact, *this);         \
  bitwise_conj_rule.rewrite_fact(fact, *this);

class graph_rulet
{
public:
  graph_rulet(expression_poolt& pool):
    expression_pool(pool)
  {
  }

  virtual bool rewrite_term(unsigned, wordlevel_factt::partitiont, 
                            class graph_axiomst&) { return true; }
  virtual bool rewrite_fact(const graph_factt&, 
                            class graph_axiomst&) { return true; }

protected:
  expression_poolt &expression_pool;
};

/*******************************************************************\

  The actual rewriting rules

\*******************************************************************/

class added_constant_rulet:public graph_rulet
{
public:
  added_constant_rulet(expression_poolt &pool): graph_rulet(pool) { }

  bool rewrite_term(unsigned index, wordlevel_factt::partitiont, 
                    class graph_axiomst&);
};

class bitseq_extract_rulet:public graph_rulet
{
public:
  bitseq_extract_rulet(expression_poolt &pool): graph_rulet(pool) { }

  bool rewrite_term(unsigned index, wordlevel_factt::partitiont, 
                    class graph_axiomst&);
};

class bit_replication_rulet:public graph_rulet
{
public:
  bit_replication_rulet(expression_poolt &pool): graph_rulet(pool) { }

  bool rewrite_term(unsigned index, wordlevel_factt::partitiont, 
                    class graph_axiomst&);
protected:
  bool simplify_concatenation(exprt&) const;
  bool simplify_replication(exprt&) const;
};

class bitvec_upcast_rulet:public graph_rulet
{
public:
  bitvec_upcast_rulet(expression_poolt &pool): graph_rulet(pool) { }

  bool rewrite_fact(const graph_factt&, class graph_axiomst&);
protected:
  bool cast_constant(exprt& constant, const typet& type) const;
};

class conditional_cast_rulet:public graph_rulet
{
public:
  conditional_cast_rulet(expression_poolt &pool): graph_rulet(pool) { }

  bool rewrite_fact(const graph_factt&, class graph_axiomst&);
protected:
  bool cast_constant(exprt& constant, const typet& type) const;
};

class struct_with_rulet:public graph_rulet
{
public:
  struct_with_rulet(expression_poolt &pool): graph_rulet(pool) { }

  bool rewrite_fact(const graph_factt&, class graph_axiomst&);
protected:
  bool rewrite_with_fact(const graph_factt&, 
                         const exprt&, const exprt&,
                         class graph_axiomst&);
  bool rewrite_struct_fact(const graph_factt&, 
                           const exprt&, const exprt&,
                           class graph_axiomst&);
};

class bitwise_conjunction_rulet:public graph_rulet
{
public:
  bitwise_conjunction_rulet(expression_poolt &pool): graph_rulet(pool) { }

  bool rewrite_fact(const graph_factt&, class graph_axiomst&);
};

class shift_rulet:public graph_rulet
{
public:
  shift_rulet(expression_poolt &pool): graph_rulet(pool) { }

  bool rewrite_fact(const graph_factt&, class graph_axiomst&);
  bool rewrite_term(unsigned index, wordlevel_factt::partitiont, 
                    class graph_axiomst&);
};

class null_pointer_cast_rulet:public graph_rulet
{
public:
  null_pointer_cast_rulet(expression_poolt &pool): graph_rulet(pool) { }

  bool rewrite_term(unsigned index, wordlevel_factt::partitiont, 
                    class graph_axiomst&);
};

#endif
