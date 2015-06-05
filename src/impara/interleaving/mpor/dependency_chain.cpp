/*******************************************************************\

Module: Dependency chain

Author: Daniel Kroening, kroening@kroening.com
        Bjorn Wachter, bjoern.wachter@gmail.com

\*******************************************************************/

#include <cassert>
#include <vector>
#include <iostream>

#include <util/i2string.h>

#include <algorithm>

#include "dependency_chain.h"


/*******************************************************************\

Function: dependency_chaint::update

  Inputs: Update transitive dependencies with respect to an access. 

 Outputs: Modified dependency chain

 Purpose:

  The update rules can be described in terms of update equations.
  The existence of dependencies or absence of a previous run of
  a thread are encoded in terms of 3 values:
 
  1  ... dependency exists
  -1 ... no dependency exists
  0  ... hasn't been executed yet
 
  The update is formally defined as follows:
  
    1.) DC_{i,i}(k)=1
    2.) DC_{i,j}(k)=-1                                            (i\neq j)
    3.) DC_{j,i}(k)=0                                             (j\neq i, DC_{j,j}(k-1)=0)
    4.) DC_{j,i)(k)= \/_{l=1..n} DC_{j,l}(k-1)=1 & DEP_{l,i}(k))  (j\neq i, DC_{j,j}(k-1)\neq 0)
    5.) DC_{p,q}(k)=DC_{p,q}(k-1)                                 (p\neq i, q\neq i)

  where DC(k-1) is dc, DC(k) is the current object.:

  Explanation:
 
    1.) Thread i always has dependency with itself
    2.) Thread j\neq i is not the current thread
    3.) There can be no dependency with j, for j has never run.
    4.) Track transitive dependencies.
    5.) No change to depencies not affected by thread i.

\*******************************************************************/

void dependency_chaint::update(const dependency_chaint& dc, 
                               const dependenciest& dep, 
                               unsigned i)
{
  n=dep.size();
  
  
  resize(n);
  
  if(n == dc.n)
    table=dc.table; // rule 5
  else
  {
    for(unsigned j=0; j<n; ++j)
    {
      for(unsigned i=0; i<n; ++i)
      {
        set(i,j,dc(i,j));
      }
    }
  }

  // rules 1. and 2.
  for(unsigned j=0; j<n; ++j)
  {
    set(i,j,-1);
  }
  
  set(i,i,1);
  
  // rule 3.
  for(unsigned j=0; j<n; ++j)
  {
    if(i==j) continue;
    
    if(dc(j,j)==0)
    {
      set(j,i,0);
    }
    else
    {
      char disj=-1;
      
      for(unsigned l=0; l<n; ++l)
      {
        if(dc(j,l)==1 && dep[l]) {
          disj=1;
          break;
        }
      }
      
      set(j,i,disj);
    }
  }
  
  assert(reads.size()==n);
  assert(writes.size()==n);
  
}


/*******************************************************************\

Function: dependency_chaint::resize

  Inputs: 

 Outputs: 

 Purpose:

\*******************************************************************/

void dependency_chaint::resize(unsigned _n)
{
  n=_n;

  table.resize(2*n*n);
  reads.resize(n);
  writes.resize(n); 
}


/*******************************************************************\

Function: dependency_chaint::select

  Inputs: thread i, DC(k) as dc_now and DC(k-1) as dc_pre

 Outputs: number of thread to execute

 Purpose:
   decide whether to select a thread for execution

    1.) S_i(0)=true
    2.) S_i(k)=/\_{j>i} DC_{j,i}(k)\neq -1 || \/_{l<i} DC_{j,l}(k-1)=1


\*******************************************************************/

bool dependency_chaint::select(unsigned i, 
                               const dependency_chaint& dc_pre, 
                               const dependency_chaint& dc_now)
{  
  // let us ignore rule 1. for now

  if(dc_now(i,i)==0)
    return true;

  /*
  if(i+1==dc_now.n)
    return false;
   */ 

  // rule 2.
  for(unsigned j=i+1; j<dc_now.n; ++j)
  {
    if(dc_now(j,i)==-1)
    {
      bool disj=false;
      
      for(unsigned l=0; l<i; ++l)
      {
        if(dc_pre(j,l)==1)
        {
          disj=true;
          break;
        }
      }  
      
      if(!disj)
        return false;
    } 
  }

  return true;
}


/*******************************************************************\

Function: dependency_chaint::pretty

  Inputs: 

 Outputs: 

 Purpose:
  Writing random access.

\*******************************************************************/

std::string dependency_chaint::pretty(const std::string& indent)
{
  std::string result;
  
  for(unsigned j=0; j<n; ++j)
  {
    result+=indent;
    for(unsigned i=0; i<n; ++i)
    {
      char entry=(*this)(i,j);
      switch(entry)
      {
        case 0:
          result+="~";
          break;
        case 1:
          result+="+";
          break;
        case -1:
          result+="-";
        default:
          break;
      }
    }
    result +="\\n";
  }
    
  return result;

}



/*******************************************************************\

Function: dependency_chaint::set

  Inputs: 

 Outputs: 

 Purpose:
  Writing random access.

\*******************************************************************/

void dependency_chaint::set(unsigned i, unsigned j, char val)
{   
    unsigned index=2*(j*n + i);
    std::vector<bool>::iterator it=table.begin()+index;
   
    *it=val>0;
    *(++it)=val<0;
}



/*******************************************************************\

Function: dependency_chaint::operator()

  Inputs: 

 Outputs: 

 Purpose:
  Reading random access.

\*******************************************************************/

char dependency_chaint::operator()(unsigned i, unsigned j) const
{
  if(i>=n || j>=n)
    return 0;
  else
  {
    unsigned index=2*(j*n + i);   
    std::vector<bool>::const_iterator it=table.begin()+index;
    return *it - *(++it);
  } 
}

/*******************************************************************\

Function: dependency_chaint::swap

  Inputs: 

 Outputs: 

 Purpose:

\*******************************************************************/

void dependency_chaint::swap(dependency_chaint& other)
{
  table.swap(other.table);
  unsigned copy=n;
  n=other.n;
  other.n=copy;
  
  reads.swap(other.reads);
  writes.swap(other.writes);
}

/*******************************************************************\

Function: dependency_chaint::operator=

  Inputs: 

 Outputs: 

 Purpose:

\*******************************************************************/

dependency_chaint& dependency_chaint::operator=(const dependency_chaint& dc)
{
  n=dc.n;
  table=dc.table;
  reads=dc.reads;
  writes=dc.writes;
  return *this;
}   


/*******************************************************************\

Function: dependency_chaint::operator<

  Inputs: 

 Outputs: 

 Purpose:

\*******************************************************************/

bool dependency_chaint::operator<(const dependency_chaint& dc)
{
  bool result=true;

  if(n!=dc.n)
  {
    result=false;
  }
  else
  {

    for(unsigned i=0; result && i<n; ++i)
    {
      for(unsigned j=0; result && j<n; ++j)
      {
        char e1=(*this)(i,j);
        char e2=dc(i,j);
        bool ok=e1==e2 || (e1==-1);
        if(!ok) {
          result=false;
        }
      }
    }
  }
  
  for(unsigned i=0; result && i<n; ++i)
  {
    result=result &&
      std::includes(writes[i].begin(), writes[i].end(),
                    dc.writes[i].begin(), dc.writes[i].end());
  }
  
  for(unsigned i=0; result && i<n; ++i)
  {
    result=result &&
      std::includes(reads[i].begin(), reads[i].end(),
                    dc.reads[i].begin(), dc.reads[i].end());
  }
                         
  return result;
}   

/*******************************************************************\

Function: dependency_chaint::operator<

  Inputs: 

 Outputs: 

 Purpose:

\*******************************************************************/

bool dependency_chaint::operator==(const dependency_chaint& dc)
{
  bool result=true;

  if(n!=dc.n)
  {
    result=false;
  }
  else
  {

    for(unsigned i=0; result && i<n; ++i)
    {
      for(unsigned j=0; result && j<n; ++j)
      {
        char e1=(*this)(i,j);
        char e2=dc(i,j);
        bool ok=e1==e2;
        if(!ok) {
          result=false;
        }
      }
    }
  }
  
  
  for(unsigned i=0; result && i<n; ++i)
  {
    result=result &&
      std::equal(writes[i].begin(), writes[i].end(),
                 dc.writes[i].begin());
  }
  
  for(unsigned i=0; result && i<n; ++i)
  {
    result=result &&
      std::equal(reads[i].begin(), reads[i].end(),
                 dc.reads[i].begin());
  }
       
  return result;
}   




