#ifdef TEST_WORDLEVEL_INTERPOLATOR

#include <namespace.h>
#include <language_util.h>
#include <mp_arith.h>
#include <arith_tools.h>
#include <rational_tools.h>

#include <std_expr.h>
#include <std_types.h>

#include <langapi/mode.h>

#include <ansi-c/ansi_c_language.h>

void test0()
{
  // (a>=b && b>=c && c>=a) && (a=d && c=e) && (e=d+1)
  // expecting interpolants (a==c), (d==e)
  
  exprt e0(">=", typet("bool"));
  exprt e1(">=", typet("bool"));
  exprt e2(">=", typet("bool"));
  exprt e3("=", typet("bool"));
  exprt e4("=", typet("bool"));
  exprt e5("=", typet("bool"));
  
  symbol_exprt a("a"), b("b"), c("c"), d("d"), e("e");
  a.type()=typet("integer");
  b.type()=typet("integer");
  c.type()=typet("integer");
  d.type()=typet("integer");
  e.type()=typet("integer");

  exprt sum("+", typet("integer"));
  exprt c0=from_integer(1, typet("integer"));
  sum.copy_to_operands(d, c0);

  // partition 1
  e0.copy_to_operands(a, b); // a >= b
  e1.copy_to_operands(b, c); // b >= c
  e2.copy_to_operands(c, a); // c >= a

  // partition 2
  e3.copy_to_operands(a, d); // a = d
  e4.copy_to_operands(c, e); // c = e

  // partition 3
  e5.copy_to_operands(e, sum); // e = d+1

  contextt ctx;
  namespacet ns(ctx);
  transitivity_interpolatort interpolator(ns);

  expr_listt el;

  exprt a0("and", typet("bool"));
  a0.copy_to_operands(e0, e1, e2);

  exprt a1("and", typet("bool"));
  a1.copy_to_operands(e3, e4);


  el.push_back(a0);
  el.push_back(a1);
  el.push_back(e5);

  interpolator.add_formulas(el);

  expr_listt interpolants;

  std::cout << "Expecting (a==c), (d==e)" << std::endl;

  if (interpolator.infer()==decision_proceduret::D_UNSATISFIABLE)
  {
    interpolator.get_interpolants(interpolants);
      
    contextt ctx;
    namespacet ns(ctx);
    for (expr_listt::const_iterator e_it=interpolants.begin();
         e_it!=interpolants.end(); e_it++)
    {
      std::cout << from_expr(ns, "", *e_it) << std::endl;
    }
  }
  else
    std::cout << "Failed to interpolate." << std::endl;
}

void test1()
{
  // (a==4) && (a != 4 && a == 5)

  exprt e0("=", typet("bool"));
  exprt e1("=", typet("bool"));
  exprt e2("=", typet("bool"));
  
  symbol_exprt a("a");
  a.type()=typet("integer");

  exprt c4=from_integer(4, typet("integer"));
  exprt c5=from_integer(5, typet("integer"));

  // partition 1
  e0.copy_to_operands(a, c4); // a == 4

  // partition 2
  e1.copy_to_operands(a, c4); e1.make_not(); // a != 4
  e2.copy_to_operands(a, c5); // a == 5

  contextt ctx;
  namespacet ns(ctx);
  transitivity_interpolatort interpolator(ns);

  expr_listt el;

  exprt a0("and", typet("bool"));
  a0.copy_to_operands(e1, e2);


  el.push_back(e0);
  el.push_back(a0);

  interpolator.add_formulas(el);

  expr_listt interpolants;

  std::cout << "Expecting one of (4>=a), (4==a)" << std::endl;

  if (interpolator.infer()==decision_proceduret::D_UNSATISFIABLE)
  {
    interpolator.get_interpolants(interpolants);
      
    contextt ctx;
    namespacet ns(ctx);
    for (expr_listt::const_iterator e_it=interpolants.begin();
         e_it!=interpolants.end(); e_it++)
    {
      std::cout << from_expr(ns, "", *e_it) << std::endl;
    }
  }
  else
    std::cout << "Failed to interpolate." << std::endl;
}

void test2()
{
  // (a==0 && a==1) && true
  // Expecting false

  exprt e0("=", typet("bool"));
  exprt e1("=", typet("bool"));
  exprt e2; e2.make_true();
  
  symbol_exprt a("a");
  a.type()=typet("integer");

  exprt c0=from_integer(0, typet("integer"));
  exprt c1=from_integer(1, typet("integer"));

  // partition 1
  e0.copy_to_operands(a, c0); // a == 0
  e1.copy_to_operands(a, c1); // a == 1

  exprt a0("and", typet("bool"));
  a0.copy_to_operands(e0, e1);

  expr_listt el;

  el.push_back(a0);
  el.push_back(e2);

  contextt ctx;
  namespacet ns(ctx);
  transitivity_interpolatort interpolator(ns);

  interpolator.add_formulas(el);

  std::cout << "Expecting false (i.e., a!=a,  0>=1)" << std::endl;

  expr_listt interpolants;

  if (interpolator.infer()==decision_proceduret::D_UNSATISFIABLE)
  {
    interpolator.get_interpolants(interpolants);
      
    contextt ctx;
    namespacet ns(ctx);
    for (expr_listt::const_iterator e_it=interpolants.begin();
         e_it!=interpolants.end(); e_it++)
    {
      std::cout << from_expr(ns, "", *e_it) << std::endl;
    }
  }
  else
    std::cout << "Failed to interpolate." << std::endl;
}

void test3()
{
  // (a!=a) && true (contradictory fact in A)
  // expecting a!=a

  exprt e0("=", typet("bool"));
  exprt e1; e1.make_true();
  
  symbol_exprt a("a");
  a.type()=typet("integer");

  // partition 1
  e0.copy_to_operands(a, a); // a == a
  e0.negate();

  contextt ctx;
  namespacet ns(ctx);
  transitivity_interpolatort interpolator(ns);

  interpolator.add_formula(e0, 0);
  interpolator.add_formula(e1, 1);

  expr_listt interpolants;

  std::cout << "Expecting (a!=a)" << std::endl;

  if (interpolator.infer()==decision_proceduret::D_UNSATISFIABLE)
  {
    interpolator.get_interpolants(interpolants);
      
    contextt ctx;
    namespacet ns(ctx);
    for (expr_listt::const_iterator e_it=interpolants.begin();
         e_it!=interpolants.end(); e_it++)
    {
      std::cout << from_expr(ns, "", *e_it) << std::endl;
    }
  }
  else
    std::cout << "Failed to interpolate." << std::endl;
}

void test4()
{
  // (s0=0 && s1=s0+1) && (s1=0)
  // interpolant should be (s1!=0)
  
  exprt e0("=", typet("bool"));
  exprt e1("=", typet("bool"));
  exprt e2("=", typet("bool"));
  
  symbol_exprt a("s0"), b("s1");
  a.type()=typet("integer");
  b.type()=typet("integer");

  exprt sum("+", typet("integer"));
  exprt c0=from_integer(0, typet("integer"));
  exprt c1=from_integer(1, typet("integer"));
  sum.copy_to_operands(a, c1);

  // partition 1
  e0.copy_to_operands(a, c0); // s0 = 0
  e1.copy_to_operands(b, sum); // s1 = s0+1

  // partition 2
  e2.copy_to_operands(b, c0); // s1 = 0

  contextt ctx;
  namespacet ns(ctx);
  transitivity_interpolatort interpolator(ns);

  expr_listt el;

  exprt a0("and", typet("bool"));
  a0.copy_to_operands(e0, e1);

  el.push_back(a0);
  el.push_back(e2);

  interpolator.add_formulas(el);

  expr_listt interpolants;

  std::cout << "Expecting (s1!=0)" << std::endl;

  if (interpolator.infer()==decision_proceduret::D_UNSATISFIABLE)
  {
    interpolator.get_interpolants(interpolants);
      
    contextt ctx;
    namespacet ns(ctx);
    for (expr_listt::const_iterator e_it=interpolants.begin();
         e_it!=interpolants.end(); e_it++)
    {
      std::cout << from_expr(ns, "", *e_it) << std::endl;
    }
  }
  else
    std::cout << "Failed to interpolate." << std::endl;
}

void test5()
{
  // (a=0 && b=a+c) && (c=1 && b=0)
  // interpolant should be (b=0+c) or (b=c) or (c=1 ==> b=1)
  std::cout << "(a=0 && b=a+c) && (c=1 && b=0)" <<std::endl;
  std::cout << "interpolant should be (b=0+c) or (b=c) or (c=1 ==> b=1)" << std::endl;
  
  exprt e0("=", typet("bool"));
  exprt e1("=", typet("bool"));
  exprt e2("=", typet("bool"));
  exprt e3("=", typet("bool"));
  
  symbol_exprt a("a"), b("b"), c("c");
  a.type()=typet("integer");
  b.type()=typet("integer");
  c.type()=typet("integer");

  exprt sum("+", typet("integer"));
  sum.copy_to_operands(a, c);

  exprt c0=from_integer(0, typet("integer"));
  exprt c1=from_integer(1, typet("integer"));

  // partition 1
  e0.copy_to_operands(a, c0); // a = 0
  e1.copy_to_operands(b, sum); // b = a+c

  // partition 2
  e2.copy_to_operands(b, c0); // b = 0
  e3.copy_to_operands(c, c1); // c = 1

  contextt ctx;
  namespacet ns(ctx);
  transitivity_interpolatort interpolator(ns);

  expr_listt el;

  exprt a0("and", typet("bool"));
  a0.copy_to_operands(e0, e1);

  exprt a1("and", typet("bool"));
  a1.copy_to_operands(e2, e3);

  el.push_back(a0);
  el.push_back(a1);

  interpolator.add_formulas(el);

  expr_listt interpolants;

  std::cout << "Expecting (b=c) or (c!=1 || b=1)" << std::endl;

  if (interpolator.infer()==decision_proceduret::D_UNSATISFIABLE)
  {
    interpolator.get_interpolants(interpolants);
      
    contextt ctx;
    namespacet ns(ctx);
    for (expr_listt::const_iterator e_it=interpolants.begin();
         e_it!=interpolants.end(); e_it++)
    {
      std::cout << from_expr(ns, "", *e_it) << std::endl;
    }
  }
  else
    std::cout << "Failed to interpolate." << std::endl;
}

void test6()
{
  // (a=b*c && d=6 && e=3 && d!=a) && (c=e && b=2)
  // interpolant should be !(b==2) || !(c==e)
  
  exprt e0("=", typet("bool"));
  exprt e1("=", typet("bool"));
  exprt e2("=", typet("bool"));
  exprt e3("=", typet("bool"));
  exprt e4("=", typet("bool"));
  exprt e5("=", typet("bool"));
  
  symbol_exprt a("a"), b("b"), c("c"), d("d"), e("e");
  a.type()=typet("integer");
  b.type()=typet("integer");
  c.type()=typet("integer");
  d.type()=typet("integer");
  e.type()=typet("integer");

  exprt mul("*", typet("integer"));
  mul.copy_to_operands(b, c);

  exprt c2=from_integer(2, typet("integer"));
  exprt c3=from_integer(3, typet("integer"));
  exprt c6=from_integer(6, typet("integer"));

  // partition 1
  e0.copy_to_operands(a, mul); // a = b*c
  e1.copy_to_operands(d, c6); // d = 6
  e2.copy_to_operands(e, c3); // e = 3
  e3.copy_to_operands(d, a); e3.negate(); // d != a

  // partition 2
  e4.copy_to_operands(c, e); // c = e
  e5.copy_to_operands(b, c2); // b = 2

  contextt ctx;
  namespacet ns(ctx);
  transitivity_interpolatort interpolator(ns);

  expr_listt el;

  exprt a0("and", typet("bool"));
  a0.copy_to_operands(e0, e1);
  a0.copy_to_operands(e2, e3);

  exprt a1("and", typet("bool"));
  a1.copy_to_operands(e4, e5);

  el.push_back(a0);
  el.push_back(a1);

  interpolator.add_formulas(el);

  expr_listt interpolants;

  std::cout << "Expecting !(b==2) || !(c==e)" << std::endl;

  if (interpolator.infer()==decision_proceduret::D_UNSATISFIABLE)
  {
    interpolator.get_interpolants(interpolants);
      
    contextt ctx;
    namespacet ns(ctx);
    for (expr_listt::const_iterator e_it=interpolants.begin();
         e_it!=interpolants.end(); e_it++)
    {
      std::cout << from_expr(ns, "", *e_it) << std::endl;
    }
  }
  else
    std::cout << "Failed to interpolate." << std::endl;
}

void test7()
{
  // an example with UIF without constants,
  // and a degenerate parent chain for the congruence 
  // (x=a+b && a=-b) && (x!=0)
  // interpolant should be 
  
  exprt e0("=", typet("bool"));
  exprt e1("=", typet("bool"));
  exprt e2("=", typet("bool"));
  
  symbol_exprt a("a"), b("b"), nb("b"), x("x");
  a.type()=typet("integer");
  b.type()=typet("integer");
  nb.type()=typet("integer");
  x.type()=typet("integer");

  exprt sum("+", typet("integer"));
  sum.copy_to_operands(a, b);

  nb.negate(); // -b
  exprt c0=from_integer(0, typet("integer"));

  // partition 1
  e0.copy_to_operands(x, sum); // x = a+b
  e1.copy_to_operands(a, nb); // a = -b

  // partition 2
  e2.copy_to_operands(x, c0); // x = 0
  e2.negate(); // x != 0

  contextt ctx;
  namespacet ns(ctx);
  transitivity_interpolatort interpolator(ns);

  expr_listt el;

  exprt a0("and", typet("bool"));
  a0.copy_to_operands(e0, e1);

  el.push_back(a0);
  el.push_back(e2);

  interpolator.add_formulas(el);

  expr_listt interpolants;

  std::cout << "Expecting failed interpolation or x=0" << std::endl;
  /* The reason for a failed interpolation is that x=a+b and 
     x!=0 do not share variables, i.e., if -b is the representative
     of a=-b, then the substitution a+b[a/-b] is never performed.
     N&O's algorithm would only work if x!=-b+b instead of x!=0 */

  if (interpolator.infer()==decision_proceduret::D_UNSATISFIABLE)
  {
    interpolator.get_interpolants(interpolants);
      
    contextt ctx;
    namespacet ns(ctx);
    for (expr_listt::const_iterator e_it=interpolants.begin();
         e_it!=interpolants.end(); e_it++)
    {
      std::cout << from_expr(ns, "", *e_it) << std::endl;
    }
  }
  else
    std::cout << "Failed to interpolate." << std::endl;
}

void test8()
{
  // a degenerate parent chain for the congruence 
  // (x=a+b && a=-b) && (x!=0)
  // interpolant should be 
  
  exprt e0("=", typet("bool"));
  exprt e1("=", typet("bool"));
  exprt e2("=", typet("bool"));
  exprt e3("=", typet("bool"));
  
  symbol_exprt a("a"), b("b"), nb("b"), x("x");
  a.type()=typet("integer");
  b.type()=typet("integer");
  nb.type()=typet("integer");
  x.type()=typet("integer");

  exprt sum("+", typet("integer"));
  sum.copy_to_operands(a, b);

  nb.negate(); // -b
  exprt c0=from_integer(0, typet("integer"));
  exprt c1=from_integer(1, typet("integer"));
  exprt cm1=from_integer(-1, typet("integer"));

  // partition 1
  e0.copy_to_operands(x, sum); // x = a+b
  e1.copy_to_operands(a, cm1); // a = -1
  e2.copy_to_operands(b, c1);  // b = 1

  // partition 2
  e3.copy_to_operands(x, c0); // x = 0
  e3.negate(); // x != 0

  contextt ctx;
  namespacet ns(ctx);
  transitivity_interpolatort interpolator(ns);

  expr_listt el;

  exprt a0("and", typet("bool"));
  a0.copy_to_operands(e0, e1);
  a0.copy_to_operands(e2);

  el.push_back(a0);
  el.push_back(e3);

  interpolator.add_formulas(el);

  expr_listt interpolants;

  std::cout << "Expecting (x==0)" << std::endl;

  if (interpolator.infer()==decision_proceduret::D_UNSATISFIABLE)
  {
    interpolator.get_interpolants(interpolants);
      
    contextt ctx;
    namespacet ns(ctx);
    for (expr_listt::const_iterator e_it=interpolants.begin();
         e_it!=interpolants.end(); e_it++)
    {
      std::cout << from_expr(ns, "", *e_it) << std::endl;
    }
  }
  else
    std::cout << "Failed to interpolate." << std::endl;
}

void test9()
{
  // false && true
  // Expecting false

  exprt e0; e0.make_false();
  exprt e1; e1.make_true();

  expr_listt el;

  el.push_back(e0);
  el.push_back(e1);

  contextt ctx;
  namespacet ns(ctx);
  transitivity_interpolatort interpolator(ns);

  interpolator.add_formulas(el);

  std::cout << "Expecting false" << std::endl;

  expr_listt interpolants;

  if (interpolator.infer()==decision_proceduret::D_UNSATISFIABLE)
  {
    interpolator.get_interpolants(interpolants);
      
    contextt ctx;
    namespacet ns(ctx);
    for (expr_listt::const_iterator e_it=interpolants.begin();
         e_it!=interpolants.end(); e_it++)
    {
      std::cout << from_expr(ns, "", *e_it) << std::endl;
    }
  }
  else
    std::cout << "Failed to interpolate." << std::endl;
}

void test10()
{
  // true && false
  // Expecting true

  exprt e0; e0.make_true();
  exprt e1; e1.make_false();

  expr_listt el;

  el.push_back(e0);
  el.push_back(e1);

  contextt ctx;
  namespacet ns(ctx);
  transitivity_interpolatort interpolator(ns);

  interpolator.add_formulas(el);

  std::cout << "Expecting true" << std::endl;

  expr_listt interpolants;

  if (interpolator.infer()==decision_proceduret::D_UNSATISFIABLE)
  {
    interpolator.get_interpolants(interpolants);
      
    contextt ctx;
    namespacet ns(ctx);
    for (expr_listt::const_iterator e_it=interpolants.begin();
         e_it!=interpolants.end(); e_it++)
    {
      std::cout << from_expr(ns, "", *e_it) << std::endl;
    }
  }
  else
    std::cout << "Failed to interpolate." << std::endl;
}

void test11()
{
  // i0=0 && i1=i0+1 && !(i1<5) && (i1==5)
  // interpolants should be i0=0, i1=1, false
  
  exprt e0("=", typet("bool"));
  exprt e1("=", typet("bool"));
  exprt e2("<", typet("bool"));
  exprt e3("=", typet("bool"));
  
  symbol_exprt i0("i0"), i1("i1");
  i0.type()=typet("integer");
  i1.type()=typet("integer");

  exprt c5=from_integer(5, typet("integer"));
  exprt c1=from_integer(1, typet("integer"));
  exprt c0=from_integer(0, typet("integer"));

  e0.copy_to_operands(i0, c0);

  exprt sum("+", typet("integer"));
  sum.copy_to_operands(i0, c1);
  e1.copy_to_operands(i1, sum);

  e2.copy_to_operands(i1, c5);
  e2.negate();

  e3.copy_to_operands(i1, c5);

  contextt ctx;
  namespacet ns(ctx);
  transitivity_interpolatort interpolator(ns);

  expr_listt el;

  el.push_back(e0);
  el.push_back(e1);
  el.push_back(e2);
  el.push_back(e3);

  interpolator.add_formulas(el);

  expr_listt interpolants;

  std::cout << "Expecting (0=i), (1=i), FALSE" << std::endl;

  if (interpolator.infer()==decision_proceduret::D_UNSATISFIABLE)
  {
    interpolator.get_interpolants(interpolants);
      
    contextt ctx;
    namespacet ns(ctx);
    for (expr_listt::const_iterator e_it=interpolants.begin();
         e_it!=interpolants.end(); e_it++)
    {
      std::cout << from_expr(ns, "", *e_it) << std::endl;
    }
  }
  else
    std::cout << "Failed to interpolate." << std::endl;
}

void test12()
{
  // a=-(x) && a!=-(y) and x=y
  // interpolant should be x!=y
  
  exprt e0("=", typet("bool"));
  exprt e1("=", typet("bool"));
  exprt e2("=", typet("bool"));
  
  symbol_exprt a("a"), x("x"), y("y");
  a.type()=typet("integer");
  x.type()=typet("integer");
  y.type()=typet("integer");

  unary_exprt fx("unary-", x, typet("integer"));
  unary_exprt fy("unary-", y, typet("integer"));

  e0.copy_to_operands(a, fx);
  e1.copy_to_operands(a, fy);
  e1.negate();

  e2.copy_to_operands(x, y);

  contextt ctx;
  namespacet ns(ctx);
  transitivity_interpolatort interpolator(ns);

  expr_listt el;

  el.push_back(e0);
  el.push_back(e1);
  el.push_back(e2);

  interpolator.add_formulas(el);

  expr_listt interpolants;

  std::cout << "Expecting a=-(x), x!=y" << std::endl;

  if (interpolator.infer()==decision_proceduret::D_UNSATISFIABLE)
  {
    interpolator.get_interpolants(interpolants);
      
    contextt ctx;
    namespacet ns(ctx);
    for (expr_listt::const_iterator e_it=interpolants.begin();
         e_it!=interpolants.end(); e_it++)
    {
      std::cout << from_expr(ns, "", *e_it) << std::endl;
    }
  }
  else
    std::cout << "Failed to interpolate." << std::endl;
}

void test13()
{
  // a=-(x) && x=z and a!=-(y) && z=y
  // interpolant should be x!=y
  
  exprt e0("=", typet("bool"));
  exprt e1("=", typet("bool"));
  exprt e2("=", typet("bool"));
  exprt e3("=", typet("bool"));
  
  symbol_exprt a("a"), x("x"), y("y"), z("z");
  a.type()=typet("integer");
  x.type()=typet("integer");
  y.type()=typet("integer");
  z.type()=typet("integer");

  unary_exprt fx("unary-", x, typet("integer"));
  unary_exprt fy("unary-", y, typet("integer"));

  e0.copy_to_operands(a, fx);
  e1.copy_to_operands(x, z);
  e2.copy_to_operands(a, fy);
  e3.copy_to_operands(y, z);
  e2.negate();

  contextt ctx;
  namespacet ns(ctx);
  transitivity_interpolatort interpolator(ns);

  exprt c0("and", typet("bool"));
  c0.move_to_operands(e0, e1);
  exprt c1("and", typet("bool"));
  c1.move_to_operands(e2, e3);

  expr_listt el;

  el.push_back(c0);
  el.push_back(c1);

  interpolator.add_formulas(el);

  expr_listt interpolants;

  std::cout << "Expecting a=-(z)" << std::endl;

  if (interpolator.infer()==decision_proceduret::D_UNSATISFIABLE)
  {
    interpolator.get_interpolants(interpolants);
      
    contextt ctx;
    namespacet ns(ctx);
    for (expr_listt::const_iterator e_it=interpolants.begin();
         e_it!=interpolants.end(); e_it++)
    {
      std::cout << from_expr(ns, "", *e_it) << std::endl;
    }
  }
  else
    std::cout << "Failed to interpolate." << std::endl;
}

void test14()
{
  // i=0 && !(i<5) and (i!=5)
  // interpolant should be false
  
  exprt e0("=", typet("bool"));
  exprt e1("<", typet("bool"));
  exprt e2("=", typet("bool"));
  
  symbol_exprt i("i");
  i.type()=typet("integer");
  exprt c0=from_integer(0, typet("integer"));
  exprt c5=from_integer(5, typet("integer"));

  e0.copy_to_operands(i, c0);
  e1.copy_to_operands(i, c5);
  e1.negate();

  e2.copy_to_operands(i, c5);
  e2.negate();

  contextt ctx;
  namespacet ns(ctx);
  transitivity_interpolatort interpolator(ns);

  exprt conjunction("and", typet("bool"));
  conjunction.move_to_operands(e0, e1);
  
  expr_listt el;

  el.push_back(conjunction);
  el.push_back(e2);

  interpolator.add_formulas(el);

  expr_listt interpolants;

  std::cout << "Expecting FALSE" << std::endl;

  if (interpolator.infer()==decision_proceduret::D_UNSATISFIABLE)
  {
    interpolator.get_interpolants(interpolants);
      
    contextt ctx;
    namespacet ns(ctx);
    for (expr_listt::const_iterator e_it=interpolants.begin();
         e_it!=interpolants.end(); e_it++)
    {
      std::cout << from_expr(ns, "", *e_it) << std::endl;
    }
  }
  else
    std::cout << "Failed to interpolate." << std::endl;
}

void test15()
{
  // (s0=0 && s1=s0+1 && s2=s1+1) and !(s2<5)
  // interpolant should be (s1!=0)
  
  exprt e0("=", typet("bool"));
  exprt e1("=", typet("bool"));
  exprt e2("=", typet("bool"));
  exprt e3("<", typet("bool"));
  
  symbol_exprt a("s0"), b("s1"), c("s2");
  a.type()=typet("integer");
  b.type()=typet("integer");
  c.type()=typet("integer");

  exprt c0=from_integer(0, typet("integer"));
  exprt c1=from_integer(1, typet("integer"));
  exprt c5=from_integer(5, typet("integer"));

  e0.copy_to_operands(a, c0); // s0=0

  exprt sum0("+", typet("integer"));
  sum0.copy_to_operands(a, c1);

  e1.copy_to_operands(b, sum0); // s1 = s0+1

  exprt sum1("+", typet("integer"));
  sum1.copy_to_operands(b, c1);

  e2.copy_to_operands(c, sum1); // s2 = s1+1

  // partition 2
  e3.copy_to_operands(c, c5); 
  e3.negate(); // !(s2 < 5)

  contextt ctx;
  namespacet ns(ctx);
  transitivity_interpolatort interpolator(ns);

  expr_listt el;

  exprt a0("and", typet("bool"));
  el.push_back(e0);
  el.push_back(e1);
  el.push_back(e2);
  el.push_back(e3);

  interpolator.add_formulas(el);

  expr_listt interpolants;

  std::cout << "Expecting  .... (s2=0)" << std::endl;

  if (interpolator.infer()==decision_proceduret::D_UNSATISFIABLE)
  {
    interpolator.get_interpolants(interpolants);
      
    contextt ctx;
    namespacet ns(ctx);
    for (expr_listt::const_iterator e_it=interpolants.begin();
         e_it!=interpolants.end(); e_it++)
    {
      std::cout << from_expr(ns, "", *e_it) << std::endl;
    }
  }
  else
    std::cout << "Failed to interpolate." << std::endl;
}

void test16()
{
  // (s0=0 && s1=s0+1 && s2=s1+1 && s3=s2+1 && !(s3<5)
  // interpolant should be (s0==0), (3>=2+s1), (3>=1+s2), (3>=s2)
  
  exprt e0("=", typet("bool"));
  exprt e1("=", typet("bool"));
  exprt e2("=", typet("bool"));
  exprt e3("=", typet("bool"));
  exprt e4("<", typet("bool"));
  
  symbol_exprt a("s0"), b("s1"), c("s2"), d("s3");
  a.type()=typet("integer");
  b.type()=typet("integer");
  c.type()=typet("integer");
  d.type()=typet("integer");

  exprt c0=from_integer(0, typet("integer"));
  exprt c1=from_integer(1, typet("integer"));
  exprt c5=from_integer(5, typet("integer"));

  e0.copy_to_operands(a, c0); // s0=0

  exprt sum0("+", typet("integer"));
  sum0.copy_to_operands(a, c1);

  e1.copy_to_operands(b, sum0); // s1 = s0+1

  exprt sum1("+", typet("integer"));
  sum1.copy_to_operands(b, c1);

  e2.copy_to_operands(c, sum1); // s2 = s1+1

  exprt sum2("+", typet("integer"));
  sum2.copy_to_operands(c, c1);

  e3.copy_to_operands(d, sum2); // s3 = s2+1

  // partition 2
  e4.copy_to_operands(d, c5); 
  e4.negate(); // !(s3 < 5)

  contextt ctx;
  namespacet ns(ctx);
  transitivity_interpolatort interpolator(ns);

  expr_listt el;

  el.push_back(e0);
  el.push_back(e1);
  el.push_back(e2);
  el.push_back(e3);
  el.push_back(e4);

  interpolator.add_formulas(el);

  expr_listt interpolants;

  std::cout << "Expecting (s0==0), (3>=2+s1), (3>=1+s2), (3>=s2)" << std::endl;

  if (interpolator.infer()==decision_proceduret::D_UNSATISFIABLE)
  {
    interpolator.get_interpolants(interpolants);
      
    contextt ctx;
    namespacet ns(ctx);

    expr_listt::const_iterator e_it=interpolants.begin();

    for (expr_listt::const_iterator e_it=interpolants.begin();
         e_it!=interpolants.end(); e_it++)
    {
      std::cout << from_expr(ns, "", *e_it) << std::endl;
    }
  }
  else
    std::cout << "Failed to interpolate." << std::endl;
}

void test17()
{
  /* 
    0  a == FALSE
    1  b == a
    2  c == d
    3  c == TRUE
    4  e == (d == (b && g))
    5  e
    
    expected interpolants:

    a == FALSE
    b == FALSE
    b == FALSE && c == d
    b == FALSE && d == TRUE
    e == FALSE
    
  */

  exprt e0("=", typet("bool"));
  exprt e1("=", typet("bool"));
  exprt e2("=", typet("bool"));
  exprt e3("=", typet("bool"));
  exprt e4("=", typet("bool"));

  symbol_exprt a("a"), b("b"), c("c"), d("d"), e("e"), g("g");
  a.type()=typet("bool");
  b.type()=typet("bool");
  c.type()=typet("bool");
  d.type()=typet("bool");
  e.type()=typet("bool");
  g.type()=typet("bool");

  exprt f; f.make_false();
  exprt t; t.make_true();

  e0.copy_to_operands(a, f); // a==FALSE
  e1.copy_to_operands(b, a); // b==a
  e2.copy_to_operands(c, d); // c==d
  e3.copy_to_operands(c, t); // c==TRUE

  exprt conj("and", typet("bool"));
  conj.copy_to_operands(b, g); // b && g

  exprt eq("=", typet("bool"));
  eq.copy_to_operands(d, conj);
  e4.copy_to_operands(e, eq);

  exprt e5=e; // same_run2

  contextt ctx;
  namespacet ns(ctx);
  transitivity_interpolatort interpolator(ns);

  expr_listt el;

  el.push_back(e0);
  el.push_back(e1);
  el.push_back(e2);
  el.push_back(e3);
  el.push_back(e4);
  el.push_back(e5);

  interpolator.add_formulas(el);

  expr_listt interpolants;

  std::cout << "Expecting  a == FALSE, b == FALSE, b == FALSE && c == d, " 
            << "b == FALSE && d == TRUE, e == FALSE" << std::endl;

  if (interpolator.infer()==decision_proceduret::D_UNSATISFIABLE)
  {
    interpolator.get_interpolants(interpolants);
      
    contextt ctx;
    namespacet ns(ctx);

    expr_listt::const_iterator e_it=interpolants.begin();

    for (expr_listt::const_iterator e_it=interpolants.begin();
         e_it!=interpolants.end(); e_it++)
    {
      std::cout << from_expr(ns, "", *e_it) << std::endl;
    }
  }
  else
    std::cout << "Failed to interpolate." << std::endl;
}

void test18()
{
  std::cout << "a=0 && b=1 && c=b*5/2 && d=a+c && d>5/2" <<std::endl;
  std::cout << "interpolant should be " 
            << "(a=0), (b=1), (c=5/2), (d=5/2)" << std::endl;
  
  exprt e0("=", typet("bool"));
  exprt e1("=", typet("bool"));
  exprt e2("=", typet("bool"));
  exprt e3("=", typet("bool"));
  exprt e4(">", typet("bool"));
  
  symbol_exprt a("a"), b("b"), c("c"), d("d");
  a.type()=typet("rational");
  b.type()=typet("rational");
  c.type()=typet("rational");
  d.type()=typet("rational");

  exprt c0=from_rational(rationalt(0));
  exprt c1=from_rational(rationalt(1));
  exprt c5=from_rational(rationalt(5)/rationalt(2));

  exprt mul("*", typet("rational"));
  mul.copy_to_operands(b, c5);

  exprt sum("+", typet("rational"));
  sum.copy_to_operands(a, c);

  e0.copy_to_operands(a, c0); // a = 0
  e1.copy_to_operands(b, c1); // b = 1
  e2.copy_to_operands(c, mul); // c = b*5
  e3.copy_to_operands(d, sum); // d = a+c
  e4.copy_to_operands(d, c5); // d > 5

  contextt ctx;
  namespacet ns(ctx);
  transitivity_interpolatort interpolator(ns);

  expr_listt el;

  el.push_back(e0);
  el.push_back(e1);
  el.push_back(e2);
  el.push_back(e3);
  el.push_back(e4);

  interpolator.add_formulas(el);

  expr_listt interpolants;

  std::cout << "Expecting (a=0), (b=1), (c=5), (d=5)" << std::endl;

  if (interpolator.infer()==decision_proceduret::D_UNSATISFIABLE)
  {
    interpolator.get_interpolants(interpolants);
      
    contextt ctx;
    namespacet ns(ctx);
    for (expr_listt::const_iterator e_it=interpolants.begin();
         e_it!=interpolants.end(); e_it++)
    {
      std::cout << from_expr(ns, "", *e_it) << std::endl;
    }
  }
  else
    std::cout << "Failed to interpolate." << std::endl;
}

void test19()
{
  // !((int)a<16) && (a<14)
  // expecting a>=16

  exprt e0("<", typet(ID_bool));
  exprt e1("<", typet(ID_bool));
  
  symbol_exprt a("a");
  a.type()=unsignedbv_typet(32);
  
  typecast_exprt tc(signedbv_typet(32));
  tc.op()=a;

  exprt c16=from_integer(16, signedbv_typet(32));
  // partition 1
  e0.copy_to_operands(tc, c16); // (int)a < 16
  e0.negate(); // a >= 16

  exprt c14=from_integer(14, unsignedbv_typet(32));
  e1.copy_to_operands(tc, c14);

  contextt ctx;
  namespacet ns(ctx);
  transitivity_interpolatort interpolator(ns);

  interpolator.add_formula(e0, 0);
  interpolator.add_formula(e1, 1);

  expr_listt interpolants;

  std::cout << "Expecting (a>=16)" << std::endl;

  if (interpolator.infer()==decision_proceduret::D_UNSATISFIABLE)
  {
    interpolator.get_interpolants(interpolants);
      
    contextt ctx;
    namespacet ns(ctx);
    for (expr_listt::const_iterator e_it=interpolants.begin();
         e_it!=interpolants.end(); e_it++)
    {
      std::cout << from_expr(ns, "", *e_it) << std::endl;
    }
  }
  else
    std::cout << "Failed to interpolate." << std::endl;
}

void test20()
{
  // (x == NULL) && (x == (void*)y) && (y == (int*)(&z)) 

  exprt e0("=", typet(ID_bool));
  exprt e1("=", typet(ID_bool));
  exprt e2("=", typet(ID_bool));

  empty_typet emptyt;
  unsignedbv_typet utype(32);
  
  symbol_exprt x("x"), y("y"), z("z");
  x.type()=pointer_typet(emptyt);
  y.type()=pointer_typet(utype);
  z.type()=utype;
  
  constant_exprt null(x.type());
  null.set(ID_value, ID_NULL);
  e0.copy_to_operands(x, null);
  
  typecast_exprt ytc(x.type());
  ytc.op()=y;
  e1.copy_to_operands(x, ytc);

  address_of_exprt zaddr(z);
  typecast_exprt zatc(y.type());
  zatc.op()=zaddr;
  e2.copy_to_operands(y, zatc);
  
  contextt ctx;
  namespacet ns(ctx);
  transitivity_interpolatort interpolator(ns);

  interpolator.add_formula(e0, 0);
  interpolator.add_formula(e1, 1);
  interpolator.add_formula(e2, 2);

  expr_listt interpolants;

  std::cout << "Expecting (x==NULL), ((void*)y==NULL)" << std::endl;

  if (interpolator.infer()==decision_proceduret::D_UNSATISFIABLE)
  {
    interpolator.get_interpolants(interpolants);
      
    contextt ctx;
    namespacet ns(ctx);
    for (expr_listt::const_iterator e_it=interpolants.begin();
         e_it!=interpolants.end(); e_it++)
    {
      std::cout << from_expr(ns, "", *e_it) << std::endl;
    }
  }
  else
    std::cout << "Failed to interpolate." << std::endl;
}

int main(int argc, char** argv)
{
  register_language(new_ansi_c_language);

  test0();
  std::cout << "==========" << std::endl;
  test1();
  std::cout << "==========" << std::endl; 
  test2();
  std::cout << "==========" << std::endl; 
  test3(); 
  std::cout << "==========" << std::endl;  
  test4();
  std::cout << "==========" << std::endl;  
  test5();
  std::cout << "==========" << std::endl;   
  test6();
  std::cout << "==========" << std::endl; 
  test7();
  std::cout << "==========" << std::endl; 
  test8(); 
  std::cout << "==========" << std::endl; 
  test9();
  std::cout << "==========" << std::endl; 
  test10();
  std::cout << "==========" << std::endl; 
  test11();
  std::cout << "==========" << std::endl;    
  test12();
  std::cout << "==========" << std::endl;   
  test13();
  std::cout << "==========" << std::endl; 
  test14();
  std::cout << "==========" << std::endl; 
  test15();
  std::cout << "==========" << std::endl; 
  test16();
  std::cout << "==========" << std::endl;     
  test17();
  std::cout << "==========" << std::endl;     
  test18();
  std::cout << "==========" << std::endl;     
  test19();
  std::cout << "==========" << std::endl;     
  test20();
  std::cout << "==========" << std::endl;     
}

#endif
