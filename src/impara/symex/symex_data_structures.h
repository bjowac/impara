/*******************************************************************\

Module: Define handling of arrays, vectors, and structs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_IMPARA_SYMEX_ARRAY_H
#define CPROVER_IMPARA_SYMEX_ARRAY_H


/*
 * Full Splitting
 * --------------
 *
 * For every entry of an array, every field of a struct
 * a new symbol is introduced.
 *
 * int a[5]={0,1,2,3,4};
 * a[1]=2;
 * assert(a[0]==1)
 *
 * becomes
 *
 * a[0]#0=0
 * a[1]#0=1
 * ...
 * a[4]#0=4
 * a[1]#1=
 *
 * Consequences:
 *
 * + potentially much fewer bits in encoding
 *   + field-sensitive encoding w.r.t. structs
 *   + entry-sensitive encoding w.r.t. arrays
 *
 * - does not allow handling by array theory in SMT
 * - need to resolve array indices concretely
 *   => requires unwinding to be precise
 */
//#define SPLIT_DATA

/*
 * monolithic encoding
 * -------------------
 *
 * Arrays/structs are monolithic blocks that are updated in one chunk:
 *
 * int a[5]={0,1,2,3,4};
 * a[1]=2;
 * assert(a[0]==1)
 *
 * becomes
 *
 * a#0={0,1,2,3,4}
 * a#1=a#0 with [1:=2]
 *
 * Consequences:
 *
 * + very simple transformation
 * + addresses need not be known concretely
 *
 * - many bits needed in encoding
 */
#define WITH_DATA

#endif
