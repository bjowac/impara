#ifndef CPROVER_IMPARA_BINSEARCH_UTIL_H
#define CPROVER_IMPARA_BINSEARCH_UTIL_H

#include <util/std_expr.h>

constant_exprt between(const constant_exprt &lower, 
                       const constant_exprt &upper);
                       
bool less_than(const constant_exprt &v1, const constant_exprt &v2);                       


constant_exprt get_max_value(const typet& type);
constant_exprt get_min_value(const typet& type);

#endif
