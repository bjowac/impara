#include <util/i2string.h>
#include <langapi/language_util.h>
#include "path_summary.h"




//#define DEBUG

#ifdef DEBUG
#include <iostream>
#endif



std::string path_summaryt::pretty(const namespacet &ns) const
{
  std::string result;

  for(accesst::const_iterator
      it=reads.begin();
      it!=reads.end();
      ++it)
  {
    const exprt &x=it->first;

    result += "R " + from_expr(ns, "", x) + " ";

    for(thread_sett::const_iterator
        it2=it->second.begin();
        it2!=it->second.end();
        ++it2)
    {
      result += i2string(*it2) + " ";
    }
  }

  for(accesst::const_iterator
      it=writes.begin();
      it!=writes.end();
      ++it)
  {
    const exprt &x=it->first;

    result += "W" + from_expr(ns, "", x) + " ";

    for(thread_sett::const_iterator
        it2=it->second.begin();
        it2!=it->second.end();
        ++it2)
    {
      result += i2string(*it2) + " ";
    }
  }


  return result;
}


