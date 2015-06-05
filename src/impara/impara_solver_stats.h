/*******************************************************************\

Module: Solver statistics

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_IMPARA_SOLVER_STATS_H
#define CPROVER_IMPARA_SOLVER_STATS_H

#include <solvers/sat/satcheck.h>
#include <util/time_stopping.h>


class impara_solver_statst
{
public:
  time_periodt time;
  unsigned total_no_calls;
  unsigned total_no_clauses;
  unsigned total_no_variables;
  unsigned max_no_clauses;
  unsigned max_no_variables;

  impara_solver_statst()
  : time(current_time()-current_time()),
    total_no_calls(0),
    total_no_clauses(0),
    total_no_variables(0),
    max_no_clauses(0),
    max_no_variables(0)
  {}

  void log_begin()
  {
 	  start_time=current_time();
  }
  
  void log_end(const satcheckt& satcheck)
  {
    ++total_no_calls;
    time+=current_time()-start_time;
    max_no_clauses=satcheck.no_clauses()>max_no_clauses ? satcheck.no_clauses() : max_no_clauses;
    max_no_variables=satcheck.no_variables()>max_no_variables ? satcheck.no_variables() : max_no_variables;
    total_no_clauses += satcheck.no_clauses();
    total_no_variables += satcheck.no_variables();
  }
  
  void output(std::ostream &out)
  {
    out << " solver time " << time << "s #runs " << total_no_calls << std::endl;
    
    if(total_no_calls > 0)
    {
      out<< " * clauses: total " << total_no_clauses 
                                 << " avg " << total_no_clauses/float(total_no_calls)
                                 << " max " << max_no_clauses << std::endl
         << " * vars: total "    << total_no_variables 
                                 << " avg " << total_no_variables/float(total_no_calls) 
                                 << " max " << max_no_variables << std::endl;  
    }
  }
  
  protected:
  absolute_timet start_time;   
};
  
#endif
