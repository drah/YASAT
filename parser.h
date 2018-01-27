/*********************************************************************
			   ================
			   CNF Parsing code
				18-760
			      Fall 2006
			   ================
**********************************************************************/

#ifndef __PARSER_H__
#  define __PARSER_H__
#include <vector>
using std::vector;


// parse_DIMACS_CNF
//
// This is the function you call to read in a DIMACS CNF file.  It
// takes (by reference) a vector of vectors of ints called `clauses',
// and it stores the clause database described in the DIMACS CNF file
// `DIMACS_cnf_file' into the structure `clauses'.  Here is an example
// that illustrates usage of this function:
//
//
// // Parse the CNF file "benchmark.cnf"
// vector<vector<int> > clauses;
// int maxVarIndex;
// parse_DIMACS_CNF(clauses, maxVarIndex, "benchmark.cnf");
//
// // Now the `clauses' structure holds the clause database, and
// // `maxVarIndex' is equal to the largest variable index appearing
// // in the input CNF file.
//
//
// You can refer to the ith clause appearing in the CNF file using the
// expression `clauses[i]'.  The jth literal of `clauses[i]' can be
// referred to using `clauses[i][j]'.  The expression `clauses.size()'
// tells you the number of clauses in the benchmark.
void parse_DIMACS_CNF(vector<vector<int> > &clauses,
		      int &maxVarIndex,
		      const char *DIMACS_cnf_file);



















/*********************************************************************
  
Our CNF parser is adapted from:

MiniSat -- Copyright (c) 2003-2005, Niklas Een, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining
a copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be
included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

**********************************************************************/


#endif
