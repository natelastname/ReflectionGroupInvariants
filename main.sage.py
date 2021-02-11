'''
Copyright (C) 2021 Nathan Nichols

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.
'''

from matrix_gps_local import finitely_generated as fin_gen

D4 = DihedralGroup(4)

'''
Inputs:
       - L, a list of objects with a .degree() method returning a non-negative int.
Ouptuts: 
       - A list of lists L' where all elements of L of degree i are in L'[i] 
'''
def sort_by_degree(L):
    deg = max(map(lambda f: f.degree(), L))
    res = [[] for i in range(0,deg+1)]
    for f in L:
        res[f.degree()].append(f)
    return res


def get_index(B, quot, mono):
    for i in range(0,len(B)):
        LHS = quot(B[i])
        RHS = quot(mono)
        if LHS == RHS:
            #print(str(LHS)+" = "+str(RHS)+"? Yes")
            return i
        else:
            #print(str(LHS)+" = "+str(RHS)+"? No")
            pass
    raise RuntimeError("Could not determine the index of %s in the list: \n%s"%(mono, B))    


'''
Inputs: 
       - f, an element ofa quotient ring
Outputs: 
       - A list of the terms of f.

This is the same thing as f.monomials() except the coefficients are not discarded.
'''
def get_terms(f):
    L = []
    while not f.is_zero():
        L.append(f.lt())
        f = f - f.lt()
    return L


'''
Inputs: 
       - B is a list of distinct monomials in a polynomial ring R which represents a basis.
       - quot is a quotient ring of R.
       - g is a matrix that acts on the variables of R.
Output:
       - A matrix for the action induced by g on the basis B. 

Note: For each b\in B, quot(g.act_on_polynomial(b)) must only consist of monomials in the K-span of B
where K = g.base_ring().
'''
def matrix_wrt_standard_monos(B, quot, g):
    gndR = g.base_ring()
    g = g.matrix()
    cols = []
    for b in B:
        col = [0 for foo in B]
        gg = quot(g.act_on_polynomial(b))
        for mono in get_terms(gg):
            # It must work in the quotient ring so that the monomials of gg are canonically identified
            # with elements of a C-basis for quot.
            assert(mono.lc() != 0)
            assert(len(mono.monomials()) == 1)
            coef = 0
            index = 0
            if (mono/mono.lc()).is_one():
                coef = mono.lc()
                index = get_index(B, quot, mono/coef)
            else:
                coef = mono.lc()
                index = get_index(B, quot, mono/coef)

            #print("coef. of %s is %s in %s"%(mono, coef, gg))
            
            col[index] = coef
        #print("calculated column: "+str(col))
        cols.append(col)
    result = transpose(matrix(gndR, cols))
    #print(result)
    return result

def run_example(MG):
    print("Computing invariants...")
    G = MG.invariant_generators()
    # It might not be neccesary to compute this GB
    print("Computing GB...")
    I = ideal(G).groebner_basis()

    gndR = G[0].parent()
    quot = gndR.quotient(I)
    
    print("Generators of R^G:")
    i = 0
    for x in G:
        i = i + 1
        print(str(i)+": "+str(x))
        
    B = Ideal(I).normal_basis()
    Bdeg = sort_by_degree(B)
    
    i = 0
    print("K-basis for the quotient ring sorted by degree:")
    for x in Bdeg:
        print(str(i)+": "+str(x))
        i = i + 1

    # Is this guarenteed to be in the same order as the character table?
    MG_rep = MG.conjugacy_classes()

    print("Action of MG on the graded components of quot:")
    for b in Bdeg:
        rep = [matrix_wrt_standard_monos(b, quot, g.representative()) for g in MG_rep]
        print("--------- action of MG on "+str(b)+":")
        char = []
        for mat in rep:
            char.append(mat.trace())
        CF = ClassFunction(MG, char)
        for comp in CF.decompose():
            print("%s*%s"%(comp[0],comp[1].values()))

    '''
    # By Proposition 4.9 in Stanley's paper, the resulting rep. is the regular rep.
    print("Action of MG on the full K-basis for quot:")
    i = 0
    for g in MG:
        i = i + 1
        mat = matrix_wrt_standard_monos(B, quot, g)
        print(str(i)+":")
        print(mat)
    '''

#############################################################################
## Examples
#############################################################################


'''
An example of what doesn't work:

The big pitfall here is that MatrixGroup returns something whose type depends
on the ring R. If R is a Number Field, the resulting type has methods that we
need. If R is something like UniversalCyclotomicField(), the resulting object
does not. The function fin_gen.MatrixGroup is a slightly modified version of
the standard MatrixGroup function that can only return correct type for this
application. 
'''
'''
W = CoxeterGroup([[1,4],[4,1]])
m = W[0].matrix()
R = m.base_ring()
MS = MatrixSpace(R, *m.dimensions())
L = [MS(x.matrix()) for x in W]
MG = fin_gen.MatrixGroup(L)
'''


'''
Below, m.base_ring() is the UniversalCyclotomicField. This is actually the
perfect choice of ring for our purposes, but the complex reflection group 
library is only set up to work with a simple extension of the rationals. 

To solve this problem, we have to construct a simple extension of Q that
contains all entries of the matrices in our representation. This is easy to
do by hand, but difficult to do automatically.
'''
W = ReflectionGroup((4,4,2))
assert(D4.is_isomorphic(W))
m = W[0].to_matrix()
R = CyclotomicField(3)
MS = MatrixSpace(R, *m.dimensions())
L = [MS(x.to_matrix()) for x in W]
MG = fin_gen.MatrixGroup(L)
print("---------------------------------")
print("ReflectionGroup((4,4,2)) = D_4:")
print("---------------------------------")
run_example(MG)


# Example: D_4 as a complex reflection group using a nice basis
R = CyclotomicField(4)
MS = MatrixSpace(R, *m.dimensions())
L = []
ii = R.gens()[0]
r = MS(matrix([[ii, 0], [0, -1*ii]]))
s = MS(matrix([[0,1],[1,0]]))
L.append(r)
L.append(s)
MG = fin_gen.MatrixGroup(L)
assert(MG.as_permutation_group().is_isomorphic(D4))
print("---------------------------------")
print("D_4 as a complex reflection group using a nice basis:")
print("---------------------------------")
#run_example(MG)


# Example: C_4 (Stanley example 2.3)
R = CyclotomicField(4)
MS = MatrixSpace(R, *m.dimensions())
L = []
ii = R.gens()[0]
r = MS(matrix([[0, 1], [-1, 0]]))
L.append(r)
MG = fin_gen.MatrixGroup(L)
print("---------------------------------")
print("C_4 (Stanley example 2.3):")
print("---------------------------------")
#run_example(MG)

# The output of invariant_generators is an h.s.o.p.
G = MG.invariant_generators()
I = ideal(G).groebner_basis()
I = Ideal(I)

gndR = G[0].parent()
quot = gndR.quotient(I)

'''
The matrix group MG has two methods for computing the generators of the 
invariant ring: "invariants_of_degree" and "invariant_generators". you'll
notice that the function invariant_generators is extremely slow compared to the
function invariants_of_degree for reflection groups that are anything beyond 
the smallest examples. There is a good reason for this:

Internally, invariant_generators uses an algorithm that computes the invariants
degree-by-degree doing essentially the same thing as the function 
invariants_of_degree. The difference is that invariant_generators knows how far
it has to go before it can stop according to some upper bound. In practical
terms, what this means is that the vast majority of the work done by 
invariant_generators is towards proving that there are no invariants of higher
degree.

It is not hard to find examples where the full set of invariants is likely found
within the first few seconds but the algorithm still continues to run for a very
long time. In such cases, it would be desirable to have a way to manually 
specify a degree limit in order to force the algorithm to terminate early. 
Unfortunately, the Singular implementation of invariant_generators does not 
have such a feature. I also have some reason to believe that the upper bound 
that it uses can be improved; the function's verbose mode sometimes prints a 
message indicating that all invariants have most likely been found long before
it terminates.
'''


