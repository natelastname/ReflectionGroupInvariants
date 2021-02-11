from matrix_gps_local import finitely_generated as fin_gen

D4 = DihedralGroup(4)



'''
Input: a list of objects with a .degree() method returning a non-negative int.
Ouptut: A list of lists L' where all elements of L of degree i are in L'[i] 
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
            print(str(LHS)+" = "+str(RHS)+"? Yes")
            return i
        else:
            print(str(LHS)+" = "+str(RHS)+"? No")
            
    

def matrix_wrt_standard_monos(B, quot, g):
    gndR = g.base_ring()
    g = g.matrix()
    print("g:")
    print(g)
    cols = []
    for b in B:
        print("-----")
        print("basis vector:"+str(b))
        col = [0 for foo in B]
        gg = g.act_on_polynomial(b)
        print("after action:"+str(gg))
        for mono in gg.monomials():
            if mono.degree() == 0:
                index = get_index(B, quot, mono)
                coef = gndR(gg.constant_coefficient())
                col[index] = coef
            else:
                index = get_index(B, quot, mono)
                coef = gndR(gg.monomial_coefficient(mono))
                col[index] = coef
                
            print("gg:"+str(gg))
            print(B)
            print(col)
        cols.append(col)
    result = transpose(matrix(gndR, cols))
    print(result)
    return result

def run_example(MG):
    G = MG.invariant_generators()
    I = ideal(G).groebner_basis()

    gndR = G[0].parent()
    quot = gndR.quotient(I)
    f0 = sum(gndR(x) for x in gndR.variable_names())
    f = f0
    
    print("Generators of R^G:")
    i = 0
    for x in G:
        i = i + 1
        print(str(i)+": "+str(x))
        
    B = Ideal(I).normal_basis()
    i = 0
    print("C-basis for the quotient ring sorted by degree:")
    for x in sort_by_degree(B):
        print(str(i)+": "+str(x))
        i = i + 1

    i = 0
    for g in MG:
        i = i + 1
        print(str(i)+":")
        matrix_wrt_standard_monos(B, quot, g)

        
    x = 1/0

        

'''
An example of what doesn't work:

The big pitfall here is that MatrixGroup returns something whose type depends
on the ring R. If R is a Number Field, the resulting type has methods that we
need. If R is something like UniversalCyclotomicField(), the resulting object
does not. The function fin_gen.MatrixGroup is a slightly modified version of
the standard MatrixGroup function that can only return the type that we need.
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
contains all entries of the matrices in our representation. 
'''
W = ReflectionGroup((4,4,2))
assert(D4.is_isomorphic(W))
m = W[0].to_matrix()
R = CyclotomicField(3)
MS = MatrixSpace(R, *m.dimensions())
L = [MS(x.to_matrix()) for x in W]
MG = fin_gen.MatrixGroup(L)
print("---------------------------------")
print("ReflectionGroup((4,4,2)):")
print("---------------------------------")
#run_example(MG)


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
run_example(MG)



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
f0 = sum(gndR(x) for x in gndR.variable_names())
f = f0


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


