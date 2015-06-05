/*******************************************************************\

Module: Dependency chain

Author: Daniel Kroening, kroening@kroening.com
        Bjorn Wachter, bjoern.wachter@gmail.com

\*******************************************************************/

#ifndef CPROVER_IMPARA_DEPENDENCY_CHAIN_H
#define CPROVER_IMPARA_DEPENDENCY_CHAIN_H

#include <set>

/* dependency chains for monotonic partial order reduction:

  Vineet Kahlon, Chao Wang, Aarti Gupta: 
  `Monotonic Partial Order Reduction: 
  An Optimal Symbolic Partial Order Reduction Technique.' 
  CAV 2009: 398-413
*/
class dependency_chaint
{
public:

  dependency_chaint(unsigned _n=1)
  : n (_n), 
    table(2*n*n, false), 
    reads(n), 
    writes(n)
  {
    set(0, 0, 1);
  }
  
  dependency_chaint(const dependency_chaint& dc)
  {
    *this=dc;
  }
        
  dependency_chaint& operator=(const dependency_chaint& dc);
  
  typedef std::vector<bool> dependenciest;

  // update dependency chain after executing thread t
  void update(
    const dependency_chaint& dc, 
    const dependenciest& dep, 
    unsigned t);

  // need to run thread t?
  static bool select(
    unsigned t, 
    const dependency_chaint& dc_pre, 
    const dependency_chaint& dc_now);

  void swap(dependency_chaint& other);
  
  void resize(unsigned n);

  bool operator<(const dependency_chaint &dc);
          
  bool operator==(const dependency_chaint &dc);        
  
  void set_reads(
    unsigned t, 
    std::set<unsigned> &s)
  {
    reads[t]=s;
  }

  void set_writes(
    unsigned t, 
    std::set<unsigned> &s)
  {
    writes[t]=s;
  }
          
  std::string pretty(const std::string& indent="");
             
protected:
  unsigned n;
  std::vector<bool> table;

  std::vector<std::set<unsigned> > reads;
  std::vector<std::set<unsigned> > writes;

  char operator()(unsigned i, unsigned j) const;
  void set(unsigned i, unsigned j, char val);
};

#endif
