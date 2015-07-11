/*******************************************************************\

Module: Inductive Strengthening

Author: Bjoern Wachter, bjoern.wachter@gmail.com


\*******************************************************************/

#include <cstdlib>
#include <algorithm>
#include <iostream>

#include <util/time_stopping.h>
#include <util/expr_util.h>
#include <util/simplify_expr.h>
#include <util/replace_expr.h>
#include <util/arith_tools.h>
#include <util/i2string.h>

#include "symex/from_ssa.h"

#include "binsearch_utils.h"
#include "impara_solver.h"


#include <langapi/language_util.h>

#include "impara_join.h"
#include "simple_checker.h"

#include "interpolate/interpolator.h"

#include "impara_path_search.h"

//#define DEBUG

void impara_path_searcht::get_model(
  decision_proceduret &dp,
  std::set<exprt> &symbols,
  modelt &model)
{
  for(std::set<exprt>::const_iterator 
          it=symbols.begin(); 
          it!=symbols.end(); 
          ++it)
  {  
    model[*it]=dp.get(*it);          
  }
}


void extend_expr_types(exprt &expr)
{
  if(expr.id()==ID_symbol) return;
  if(expr.id()==ID_index) return;
  if(expr.id()==ID_unary_minus)
  {
    extend_expr_types(expr.op0());
    typet new_type = expr.op0().type();
    if(new_type.id()==ID_signedbv) 
    {
      signedbv_typet &new_typebv = to_signedbv_type(new_type);
      new_typebv.set_width(new_typebv.get_width()+1); 
    }
    else if(new_type.id()==ID_unsignedbv) 
    {
      unsignedbv_typet &old_type = to_unsignedbv_type(new_type);
      new_type = signedbv_typet(old_type.get_width()+1); 
    }
    expr = unary_minus_exprt(typecast_exprt(expr.op0(),new_type),new_type);
    return;
  }
  if(expr.id()==ID_plus || expr.id()==ID_minus)
  {
    extend_expr_types(expr.op0());
    extend_expr_types(expr.op1());
    unsigned size0 = 0, size1  = 0;
    if(expr.op0().type().id()==ID_signedbv) 
      size0 =  to_signedbv_type(expr.op0().type()).get_width();
    if(expr.op0().type().id()==ID_unsignedbv) 
      size0 =  to_unsignedbv_type(expr.op0().type()).get_width();
    if(expr.op1().type().id()==ID_signedbv) 
      size1 =  to_signedbv_type(expr.op1().type()).get_width();
    if(expr.op1().type().id()==ID_unsignedbv) 
      size1 =  to_unsignedbv_type(expr.op1().type()).get_width();
    assert(size0>0); assert(size1>0); //TODO: implement floats
    typet new_type = expr.op0().type();
    if(expr.op0().type().id()==expr.op1().type().id())
    {
     if(new_type.id()==ID_signedbv) 
       to_signedbv_type(new_type).set_width(std::max(size0,size1)+1);
     else if(new_type.id()==ID_unsignedbv) 
     {
       if(expr.id()==ID_minus) 
         new_type = signedbv_typet(std::max(size0,size1)+1);
       else 
         to_unsignedbv_type(new_type).set_width(std::max(size0,size1)+1);
     }
    }
    else
    {
     if(new_type.id()==ID_signedbv) 
       to_signedbv_type(new_type).set_width(size0<=size1 ? size1+2 : size0+1);
     else if(new_type.id()==ID_unsignedbv) 
       new_type = signedbv_typet(size1<=size0 ? size0+2 : size1+1);
    }
    if(expr.id()==ID_plus)
      expr = plus_exprt(typecast_exprt(expr.op0(),new_type),
                        typecast_exprt(expr.op1(),new_type));
    else if(expr.id()==ID_minus)
      expr = minus_exprt(typecast_exprt(expr.op0(),new_type),
                         typecast_exprt(expr.op1(),new_type));
    return;
  }
  if(expr.id()==ID_mult)
  {
    extend_expr_types(expr.op0());
    extend_expr_types(expr.op1());
    unsigned size0 = 0, size1  = 0;
    if(expr.op0().type().id()==ID_signedbv) 
      size0 =  to_signedbv_type(expr.op0().type()).get_width();
    if(expr.op0().type().id()==ID_unsignedbv) 
      size0 =  to_unsignedbv_type(expr.op0().type()).get_width();
    if(expr.op1().type().id()==ID_signedbv) 
      size1 =  to_signedbv_type(expr.op1().type()).get_width();
    if(expr.op1().type().id()==ID_unsignedbv) 
      size1 =  to_unsignedbv_type(expr.op1().type()).get_width();
    assert(size0>0); assert(size1>0); //TODO: implement floats
    typet new_type = expr.op0().type();
    if(expr.op0().type().id()==expr.op1().type().id())
    {
     if(new_type.id()==ID_signedbv) 
       to_signedbv_type(new_type).set_width(size0 + size1);
     else if(new_type.id()==ID_unsignedbv) 
     {
       to_unsignedbv_type(new_type).set_width(size0 + size1);
     }
    }
    else
    {
     if(new_type.id()==ID_signedbv) 
       to_signedbv_type(new_type).set_width(size0<=size1 ? size0 + size1+1 : size0+size1);
     else if(new_type.id()==ID_unsignedbv) 
       new_type = signedbv_typet(size1<=size0 ? size0+size1+1 : size0+size1);
    }
    expr = mult_exprt(typecast_exprt(expr.op0(),new_type),typecast_exprt(expr.op1(),new_type));
    return;
  }
}




struct row_templatet
{

  typedef exprt rowt;
  typedef std::vector<rowt> templatet;
  typedef constant_exprt row_valuet; // "bound"


  templatet templ;

  class templ_valuet : public std::vector<row_valuet> 
  {
  };
     
     
  constant_exprt get_min_row_value(size_t row)
  {
    return get_min_value(templ[row].type());
  }   

  constant_exprt get_max_row_value(size_t row)
  {
    return get_max_value(templ[row].type());
  }   
     
  void initialise(templ_valuet &val, replace_mapt &concrete)
  {
    val.resize(templ.size());
    
    for(size_t i=0; i<templ.size(); ++i)
    {
      exprt tmp=templ[i];
    
      replace_expr(concrete, tmp);
      
      exprt tmp2=simplify_expr(tmp, ns);
      
      if(tmp2.id()!=ID_constant)
        tmp2=get_max_value(tmp2.type());
      
      val[i]=to_constant_expr(tmp2);
    }
  }
 
  
  void set_row_value(templ_valuet &val, size_t row, const row_valuet &row_val)
  {
    val[row]=row_val;
  }
  
  exprt get_row_symb_value(size_t row)
  {
    assert(row<templ.size());
    return symbol_exprt("symb::bound"+i2string(row), templ[row].type());
  }
  
     
  exprt get_row_pre_constraint(size_t row, const exprt &row_value)
  {
    bool non_trivial=get_max_row_value(row)!=row_value;

    return non_trivial ?
	(exprt) binary_relation_exprt(templ[row],ID_le,row_value) : true_exprt();
  }

  exprt get_row_post_constraint(size_t row, const exprt &row_value)
  {
    exprt tmp=get_row_pre_constraint(row, row_value);
    replace_expr(post, tmp);
    return tmp;
  }

  exprt get_row_pre(size_t row)
  {
    return templ[row];
  }

  exprt get_row_post(size_t row)
  {
    exprt tmp=templ[row];
    replace_expr(post, tmp);
    return tmp;
  }

  bool is_top(const templ_valuet &value, size_t row)
  {
    return !less_than(value[row],get_max_row_value(row));
  }

  // /\ dest
  void make_pre(const templ_valuet &value, exprt::operandst &dest)
  {
    dest.resize(templ.size());
  
    for(size_t i=0; i<templ.size(); ++i)
    {
      if(is_top(value, i))
        dest[i]=true_exprt();
      else
        dest[i]=get_row_pre_constraint(i, value[i]);
    }
  }
    
  // \/ dest
  void make_negated_post(const templ_valuet &value,
                         exprt::operandst &dest_val, 
                         exprt::operandst &dest_cond
  
  )
  {
    dest_val.resize(templ.size());
    dest_cond.resize(templ.size());

    for(size_t i=0; i<templ.size(); ++i)
    {
      exprt tmp2=templ[i];
      replace_expr(post, tmp2);      
      dest_val[i]=tmp2;
      exprt tmp=get_row_post_constraint(i, value[i]);      
      dest_cond[i]=not_exprt(tmp);
    }
  }
  
  const namespacet &ns;  
  replace_mapt post; 

  typedef std::set<exprt> expr_sett;
  expr_sett new_symb;
  
  enum domain_kindt {INTERVALS, ZONES, OCTAGONS, DIFFERENCE};


  constant_exprt get(decision_proceduret &dp, size_t row)
  {
    exprt row_expr=dp.get(templ[row]);
    
    simplify(row_expr, ns);
              
    return to_constant_expr(row_expr);
  }

  
  row_templatet(const namespacet &__ns, 
                const std::string &domain_name,
                expr_sett &symb,
                replace_mapt &__post)
  : ns(__ns),
    post(__post)
  {
    domain_kindt domain_kind;
    if(domain_name=="ZONES")
      domain_kind=ZONES;
    else if(domain_name=="INTERVALS")
      domain_kind=INTERVALS;
    else if(domain_name=="OCTAGONS")
      domain_kind=OCTAGONS;
    else if(domain_name=="DIFFERENCE")
      domain_kind=DIFFERENCE;
    else
      domain_kind=DIFFERENCE; //default

    // filter out all things non-numerical
    for(expr_sett::const_iterator it=symb.begin(); it!=symb.end(); ++it)
    {
      const exprt &expr=*it;
      const typet &type=expr.type();
      if(type.id()==ID_unsignedbv || type.id()==ID_signedbv)
      {
        new_symb.insert(expr);
      }
    }

    for(expr_sett::const_iterator it1=new_symb.begin(); it1!=new_symb.end(); ++it1)
    {
      const exprt &var1=*it1;
    
      // x   
      if(domain_kind==OCTAGONS || domain_kind==ZONES || domain_kind==INTERVALS)
      {
        exprt s_expr(var1);
        extend_expr_types(s_expr);
        templ.push_back(s_expr);
      }
      
      // - x   
      if(domain_kind==OCTAGONS || domain_kind==ZONES || domain_kind==INTERVALS)
      {
        unary_minus_exprt s_expr(var1, var1.type());
        extend_expr_types(s_expr);
        templ.push_back(s_expr);
      }
      
      for(expr_sett::const_iterator it2=new_symb.begin(); it2!=it1; ++it2)
      {
        const exprt &var2=*it2;  

        // x - y
        if(domain_kind==OCTAGONS || domain_kind==ZONES || domain_kind==DIFFERENCE)
        {
          minus_exprt m_expr(var1,var2);
          extend_expr_types(m_expr);
          templ.push_back(m_expr);
        }
        
        // y - x      
        if(domain_kind==OCTAGONS || domain_kind==ZONES || domain_kind==DIFFERENCE)
        {
          minus_exprt m_expr(var2,var1);
          extend_expr_types(m_expr);
          templ.push_back(m_expr);
        }
        
        // x + y
        if(domain_kind==OCTAGONS)
        {
          plus_exprt m_expr(var1,var2);
          extend_expr_types(m_expr);
          templ.push_back(m_expr);
        }
        
        // -x - y
        if(domain_kind==OCTAGONS)
        {
          minus_exprt p_expr(unary_minus_exprt(var1,var1.type()), var2);
          extend_expr_types(p_expr);
          templ.push_back(p_expr);
        }
      } // for
    } // for
  } // constructor
  
  std::string pretty()
  {
    std::string result="Template\n";
    for(unsigned i=0; i<templ.size(); ++i)
    {
       result+= "  " + from_expr(ns, "  ", templ[i]) + " < ... \n";
    }
    return result;
  }
};


struct row_solvert
{
  typedef impara_solver_no_simplifiert::contextt contextt;

  const namespacet &ns;

  std::vector<constant_exprt> model;

  void get_model()
  {
    for(unsigned i=0; i<nr_rows; ++i)
    {
      constant_exprt val=row_template.get(solver, i);
      constant_exprt old_val=model[i];
      model[i]=less_than(old_val, val) ? val : old_val;
    }
  }



  row_solvert(const namespacet &__ns,
              impara_solver_no_simplifiert    &__solver,
              row_templatet  &__row_template,
              unsigned _limit=1024)
  : ns(__ns),
    solver         (__solver),
    row_template(__row_template),
    nr_rows(row_template.templ.size()),
    limit(_limit)
  {
    model.resize(nr_rows);

    for(unsigned i=0; i<nr_rows; ++i)
    {
      model[i]=row_template.get_min_row_value(i);
    }

#if 0
    for(unsigned r=0; r<nr_rows; ++r)
    {
      bvt bv=solver.convert_bv(row_template.get_row_pre(r));

      for(unsigned i=0; i<bv.size(); ++i)
      {
	if(!bv[i].is_constant())
	{
	  solver.set_polarity(bv[i], true);
	}
      }
    }
#endif
  }

  constant_exprt widen(const constant_exprt &value,
                   const constant_exprt &bound,
                   unsigned row)
  {
    constant_exprt threshold=from_integer(1024, value.type());

    if(height[row]>limit)
      return bound;
    else
      return value;
  }


  exprt fixpoint(row_templatet::templ_valuet &val)
  {
    size_t row=0;

    height.resize(0);
    height.resize(nr_rows,0);

    while(!is_fixpoint (val, row))
    {   
      iter(val, row);
    }

    exprt::operandst pre;
    row_template.make_pre(val, pre);
  
    return conjunction(pre);
  }

  exprt abstract(row_templatet::templ_valuet &val)
  {
    height.resize(0);
    height.resize(nr_rows,0);

    val.resize(nr_rows);
     
    for(unsigned row=0; row<nr_rows; ++row)
    {
      extend(val, row);
    }
  
    exprt::operandst pre;
    row_template.make_pre(val, pre);
  
    return conjunction(pre);
  }

    
  void extend(row_templatet::templ_valuet &val, 
              size_t row)
  {
    contextt context=solver.new_context();

    constant_exprt lower=model[row];
    constant_exprt upper=row_template.get_max_row_value(row);
    
    exprt symb_value=row_template.get_row_symb_value(row); 
     
    exprt cond=
      binary_relation_exprt(row_template.get_row_pre(row),ID_ge,symb_value);
    
    solver.set_to_context(context, cond, true);
     
    bin_search(val, row_template.get_row_pre(row), row, lower, upper, symb_value); 
     

    solver.set_context(false);
  }
  
  bool is_fixpoint(row_templatet::templ_valuet &val, 
                   size_t &row)
  {
    bool result=true;

    // context
    contextt context=solver.new_context();

    exprt::operandst pre;
    row_template.make_pre(val, pre);
   
    for(size_t i=0; i<pre.size(); ++i)
    {
      solver.set_to_context(context, pre[i], true);
    }
    
    exprt::operandst post_val;
    exprt::operandst post_cond;
    
    row_template.make_negated_post(val, post_val, post_cond);
    
    strategy_cond_literals.resize(post_cond.size());

    for(unsigned i = 0; i<post_cond.size(); i++)
    {  
      strategy_cond_literals[i] = solver.convert(post_cond[i]);
      //solver.set_frozen(strategy_cond_literals[i]);
      post_cond[i] = literal_exprt(strategy_cond_literals[i]);
    }
    
    solver.set_to_context(context, disjunction(post_cond), true);
    
    if(solver.dec_solve() == decision_proceduret::D_SATISFIABLE) //improvement check
    { 
      for(row=0; row<strategy_cond_literals.size(); row++)
      {
        if(solver.l_get(strategy_cond_literals[row]).is_true()) 
        {     
          get_model();
          break;  // we've found a row to improve
        }
      }

      result=false;
    }  

    // finish context
    solver.set_context(false);
    return result;
  }
  
  void iter(row_templatet::templ_valuet &val, 
            size_t row)
  {
    contextt context=solver.new_context();
  
    constant_exprt lower=model[row];
    constant_exprt upper=row_template.get_max_row_value(row);
    
    exprt::operandst pre;
    row_template.make_pre(val, pre);
   
    exprt symb_value=row_template.get_row_symb_value(row);
          
    pre[row]=row_template.get_row_pre_constraint(row, symb_value); 
   
    for(size_t i=0; i<pre.size(); ++i)
    {
      solver.set_to_context(context, pre[i], true);
    }
    
    exprt post_cond=
      binary_relation_exprt(
        row_template.get_row_post(row),ID_ge,symb_value);
  
    solver.set_to_context(context, post_cond, true);
     
    bin_search(val, row_template.get_row_post(row), row, 
               lower, upper, symb_value);

    solver.set_context(false);
  }

  void bin_search(row_templatet::templ_valuet &val,
                  const exprt &objective,
                  size_t row,
                  constant_exprt &lower, 
                  constant_exprt &upper, 
                  const exprt &symb_value)
  {   

    while(less_than(lower,upper))   
    {           
      constant_exprt middle = between(lower,upper);
      if(!less_than(lower,middle)) middle = upper;

      exprt tmp;

      exprt c=equal_exprt(symb_value, middle);

      contextt iteration_context=solver.new_context();
      solver.set_to_context(iteration_context, c, true);
      
      if(solver.dec_solve() == decision_proceduret::D_SATISFIABLE) 
      {   
      	get_model();

      	tmp=solver.get(objective);
      	simplify(tmp, ns);

      	lower=less_than(model[row], middle) ? middle : model[row];
      }
      else 
      {        
        if(!less_than(middle,upper)) middle=lower;
        upper=middle; 
      }
            
      lower=widen(lower, upper, row);

      ++height[row];

      #ifdef DEBUG
      std::cout << "binsearch row: " << row
                << " constraint " << from_expr(ns, "", row_template.get_row_pre_constraint(row, symb_value))
                << " lower : " << from_expr(ns, "", lower)
                << " middle: " << from_expr(ns, "", middle)
                << " upper : " << from_expr(ns, "", upper)
                << " tmp : " << from_expr(ns, "", tmp)
                << std::endl;
      #endif



      solver.set_context(false); 
    }
   
//    #ifdef DEBUG
    std::cout << "binsearch row: " << row
        << " constraint " << from_expr(ns, "", row_template.get_row_pre_constraint(row, symb_value))
	<< " lower : " << from_expr(ns, "", lower)
                << " " 
                << " upper : " << from_expr(ns, "", upper) 
                << std::endl;
//    #endif

    row_template.set_row_value(val, row, lower);
  }

  impara_solver_no_simplifiert &solver;
  row_templatet &row_template;

  unsigned nr_rows;

  unsigned limit;

  std::vector<unsigned > height;

  //handles on values to retrieve from model
  bvt strategy_cond_literals;
  exprt::operandst strategy_value_exprs;
};

class poly_templatet
{
  public:

  poly_templatet(
    const std::set<exprt>& input,
    replace_mapt &vars,
    unsigned poly_width=32)
    : coeff_nr(0)
  {

    symbol_exprt loop_counter = symbol_exprt ("polynomial::loop_counter",
      unsignedbv_typet(poly_width));
      
    exprt::operandst operands;  

    for(replace_mapt::const_iterator it=vars.begin(); it!=vars.end(); ++it)
    {
      symbol_exprt var=to_symbol_expr(it->second);
  
      unsigned width=to_bitvector_type(var.type()).get_width();        
  
      if(var.type().id()==ID_pointer)
        width=32;

      unsigned degree=0;  
        
      exprt sum0=nil_exprt();  
        
      for(std::set<exprt>::const_iterator
          it=input.begin();
          it!=input.end();
          ++it)
      {
        exprt param=*it;
        
        
        
        std::string coeff_name="polynomial::coeff@"+i2string(degree)+"#"+i2string(coeff_nr++);
      
        symbol_exprt coeff= 
          fresh_coeff(0,width);

        coefficients.push_back(coeff);
        
        exprt product=mult_exprt(coeff, param);
        
        if(sum0.is_nil())
          sum0=product;
        else
          sum0=plus_exprt(sum0, product);
      }
      
      exprt sum1=nil_exprt();
      
      for(std::set<exprt>::const_iterator
          it=input.begin();
          it!=input.end();
          ++it)
      {
        exprt param=*it;
        
        exprt coeff=
          fresh_coeff(1,width);
        
        coefficients.push_back(coeff);
        
        exprt product=mult_exprt(coeff, param);
        
        if(sum1.is_nil())
          sum1=product;
        else
          sum1=plus_exprt(sum1, product);
      }
      
      std::string coeff_name="polynomial::coeff@"+i2string(degree)+"#"+i2string(coeff_nr++);
      
      sum1=plus_exprt(sum1, fresh_coeff(1, width));
      
      operands.push_back(equal_exprt(var, plus_exprt(sum0, mult_exprt(loop_counter, sum1))));
    }  
    
    poly=conjunction(operands);
  }



  exprt poly;
  std::vector<exprt> coefficients;

  protected:
     
  unsigned coeff_nr;
          
  symbol_exprt fresh_coeff(
    unsigned degree,
    unsigned width)
  {
    std::string coeff_name="polynomial::coeff@"+i2string(degree)+"#"+i2string(coeff_nr++);
  
    return symbol_exprt(coeff_name,
      signedbv_typet(width));
  }
      
  
};


bool impara_path_searcht::strengthen(
          statet &state,
          decision_proceduret &sat_dp,
          simple_checkert &simple_checker,
          node_reft ancestor,
          exprt& assumption, 
          exprt& conclusion,
          impara_solver_statst& solver_stats)   
{       

  #ifdef DEBUG
  std::cout << "Inductive Strengthening" << std::endl;
  #endif

  bool result=false;

  // propagation
  propagationt ancestor_prop(ns, ancestor->history);
  
  
  exprt property(conclusion);

  replace_mapt vars;
  std::set<exprt> input;

  state.history.get_symbols(input, vars, 
                            ancestor); 
  
  modelt cti;

  get_model(sat_dp, input, cti);

  simple_checker.propagation.set_hidden(false);


  std::set<exprt> bounds;

  // potential bounds are not modified by loop
  for(std::set<exprt>::const_iterator 
       it=input.begin(); 
       it!=input.end(); 
       ++it)
  {
    const symbol_exprt &symbol(to_symbol_expr(*it));
    if(vars.find(symbol)==vars.end())
      bounds.insert(symbol);
  }
    
  replace_mapt concrete_state;
  
  for(std::set<exprt>::const_iterator it=input.begin(); 
      it!=input.end(); ++it)
  {
    const symbol_exprt &symbol(to_symbol_expr(*it));
    concrete_state[symbol]=ancestor_prop(symbol);
  }
  
   
  impara_solver_no_simplifiert solver(ns);

  state.history.convert(solver,
    ancestor);

  // initialise the solver for initialisation
  impara_solver_no_simplifiert init_solver(ns);
  {
    std::vector<literalt> guard_literals3;
    std::vector<exprt> guard_exprs;
    
    ancestor->history.convert(init_solver,
      initial_node_ref);
      
  }

  // initialising the solver for induction
  impara_solver_no_simplifiert templ_solver(ns);
  {

    std::vector<literalt> guard_literals2;
    
    state.history.convert(templ_solver,
      ancestor);
      
  }
  
  row_templatet row_temp(ns, 
                options.get_option("strengthen-domain"),
                input,
                vars);

  std::cout << row_temp.pretty() << std::endl;

  bool repeat=true;

  while(repeat)
  {

    repeat=false;

    bool reachable=true;

    exprt predicate;            
    predicate.make_nil();
    
    
    row_templatet::templ_valuet val;
    
    // get initial abstraction
    {
      impara_solver_no_simplifiert::contextt context=init_solver.new_context();
      row_solvert row_solver(ns, init_solver, row_temp);
    
      init_solver.set_to_context(context, assumption, true);
      
      predicate=row_solver.abstract(val);

      init_solver.set_context(false);

      std::cout << "=======================" << std::endl;
      std::cout << "INITIAL VALUE: " << from_expr(ns, "", predicate) << std::endl;
    
    }
    
    // compute fixpoint
    {
      impara_solver_no_simplifiert::contextt context=templ_solver.new_context();
      row_solvert row_solver(ns, templ_solver, row_temp);
    
      templ_solver.set_to_context(context, assumption, true);
      
      predicate=row_solver.fixpoint(val);

      templ_solver.set_context(false);

      std::cout << "=======================" << std::endl;
      std::cout << "FIXPOINT: " << from_expr(ns, "", predicate) << std::endl;
    }  
    


    std::cout << "CTI " << std::endl;

    // check if cti is reachable
    for(std::set<exprt>::const_iterator 
            it=input.begin(); 
            it!=input.end(); 
            ++it)
    {
      const exprt &symbol(*it);
      exprt prop_value(ancestor_prop(symbol));
      
      exprt cti_val=cti[symbol];
      
      if(cti_val!=prop_value)
        reachable=false;
      
      std::cout << "   " << from_expr(ns, "", symbol) << " = " 
                << from_expr(ns, "", cti_val)
                << " value at loop head " << from_expr(ns, "", prop_value) 
                << " " << (vars.find(symbol)!=vars.end() ? "MODIFIED" : "INVARIANT") << std::endl;
    }

    std::cout << (reachable ? "reachable" : "unreachable") << " CTI " << std::endl;
      

    if(predicate.is_not_nil())
    {
      // relative non-inductiveness
      exprt tmp=true_exprt();
    
      exprt predicate_post=state.read_no_propagate(from_ssa(predicate));

      // refine inductiveness query
      impara_conjoin(predicate, assumption, ns);
      impara_conjoin(predicate_post, conclusion, ns);

      impara_solver_no_simplifiert::contextt context=solver.new_context();

      // start condition?
      solver.set_to_context(context, assumption, true);

      // check if cond fails
      solver.set_to_context(
          context, conclusion
/*          do_simplify ? 
            simple_checker.propagation(conclusion) : conclusion */,
          false
      );


      interpolate(
        state,
        ancestor->history,
        ancestor,
        initial_node_ref,
        tmp,
        predicate);

      std::cout << "Property " << from_expr(ns, "", property) << std::endl;
      std::cout << "Strengthened: " << from_expr(ns, "", assumption) << std::endl
          << "              " << from_expr(ns, "",conclusion) << std::endl;    
      
      if(solver.dec_solve()==decision_proceduret::D_SATISFIABLE)
      {
        repeat=true;
        
        cti.clear();

        get_model(solver, input, cti);

        solver.set_context(false);
        repeat=false; // refinement not implemented

        std::cout << "Unrolling at N" << ancestor->number << std::endl;

      }
      else
      {
        std::cout << "Inductive at N" << ancestor->number << std::endl;

        result=true;
        repeat=false;
      }          
    }

    std::cout << "Predicate " << from_expr(ns, "", predicate) << std::endl;



  }

  return result;
}
