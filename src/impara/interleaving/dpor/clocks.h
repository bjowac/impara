/*******************************************************************\

Module: Dependency chain

Author: Daniel Kroening, kroening@kroening.com
        Bjorn Wachter, bjoern.wachter@gmail.com

\*******************************************************************/

#ifndef CPROVER_IMPARA_CLOCKS_H
#define CPROVER_IMPARA_CLOCKS_H


#include "util/i2string.h"
#include <vector>

class clockst
{
public:

  clockst(unsigned _size)
    : clock_vector(_size, 0) {
  }
          
  void max(const clockst &other)
  {
    assert(other.clock_vector.size()==clock_vector.size());
    for(unsigned i=0; i<clock_vector.size(); ++i)
    {
      unsigned value=clock_vector[i];
      unsigned other_value=other.clock_vector[i];
      unsigned max_value=value < other_value ? other_value : value;
      clock_vector[i]=max_value;
    }
  }
 
  unsigned &operator[](unsigned pos)
  {  
    return clock_vector[pos];
  }
  
  
  clockst &operator=(const clockst &other)
  {
    clock_vector=other.clock_vector;
    return *this;
  }
   
  std::string pretty(const std::string& indent="")
  {
    std::string result;
  
    for(unsigned i=0; i< clock_vector.size(); ++i)
    {
      result += i2string(clock_vector[i]) + " ";
    }
    
    return result;
  }
           
  size_t size() const { return clock_vector.size(); }
         
protected:
  std::vector<unsigned> clock_vector;
};

#endif
