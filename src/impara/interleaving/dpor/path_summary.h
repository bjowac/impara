/*******************************************************************\

Module: 

Author: Bjorn Wachter

\*******************************************************************/

#ifndef CPROVER_IMPARA_PATH_SUMMARY_H
#define CPROVER_IMPARA_PATH_SUMMARY_H

#include <set>
#include <vector>

#include <util/namespace.h>
#include <util/std_expr.h>

class path_summaryt {
  public:

  typedef exprt memt;
  typedef std::set<unsigned> thread_sett;
  typedef hash_map_cont<memt, thread_sett, irep_full_hash, irep_full_eq> accesst;

  accesst reads;  
  accesst writes;
  
  typedef hash_map_cont<unsigned, unsigned> thread_creatort;
  thread_creatort thread_creator;
 
  inline void update(const memt &mem, unsigned thread, bool read)
  {
    thread_sett &thread_set=(read ? reads : writes)[mem];
    thread_set.clear();
    thread_set.insert(thread);
  }

  void join(path_summaryt &other)
  {
    for(accesst::const_iterator it=other.reads.begin();
        it!=other.reads.end(); ++it)
    {
      const thread_sett &thread_set=it->second;
      reads[it->first].insert(thread_set.begin(), thread_set.end());
    }

    for(accesst::const_iterator it=other.writes.begin();
        it!=other.writes.end(); ++it)
    {
      const thread_sett &thread_set=it->second;
      writes[it->first].insert(thread_set.begin(), thread_set.end());
    }
    
    for(thread_creatort::const_iterator 
        it=other.thread_creator.begin();
        it!=other.thread_creator.end();
        ++it)
    {
      thread_creator[it->first]=it->second;
    }
  }

  
  std::string pretty(const namespacet &ns) const;
};

#endif
