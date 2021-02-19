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
from sage.all import *

'''
Inputs:
       - L, a list of objects w/ a .degree() method returning a non-negative int
Ouptuts: 
       - A list of lists L' where all elements of L of degree i are in L'[i] 
'''
def sort_by_degree(L):
    deg = max(map(lambda f: f.degree(), L))
    res = [[] for i in range(0,deg+1)]
    for f in L:
        res[f.degree()].append(f)
    return res

# probably only useful interally
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

'''
Inputs: 
       - A reflection group returned by Chevie. (e.g., "ReflectionGroup((1,1,4))")
Output:
       - A matrix group for which the method .invariant_generators() is defined
'''
def to_matrix_gp(W):
    '''
    Below, m.base_ring() is the UniversalCyclotomicField. This is actually the
    perfect choice of ring for our purposes, but the complex reflection group 
    library is only set up to work with a simple extension of the rationals. 

    To solve this problem, we have to construct a simple extension of Q that
    contains all entries of the matrices in our representation.
    '''
    gp_lcm = 1
    for m in W:
        M = m.to_matrix()
        MS = M.matrix_space()
        order = 1
        while True:
            M = M * (m.to_matrix())
            order = order + 1
            if M == MS(1):
                break
            
        gp_lcm = lcm(gp_lcm, order)

    gndR = CyclotomicField(gp_lcm)
    m = W[0].to_matrix()
    MS = MatrixSpace(gndR, *m.dimensions())
    L = [MS(x.to_matrix()) for x in W]
    MG = fin_gen.MatrixGroup(L)

    return MG
