#!/usr/bin/env sage -python3
from sage.all import *
import invariant_generators as inv_gens

# Specify a reflection group using a Coxeter matrix and compute the invariants.
# This works well and the base ring of C is exactly what it ought to be. However,
# only real reflection groups are fully specified by a Coxeter matrix (I believe.)
C = CoxeterGroup([[1,4],[4,1]])
gndR = PolynomialRing(C.base(),'x,y', order='degrevlex')
#inv = inv_gens.invariant_generators(C)
#I = gndR.ideal(inv)
#f = sum(gndR.gens())

class refl_wrapper:
    def __init__(self, W):
        #self.UCF = UniversalCyclotomicField()

        # This is hard coded for now
        self.R = QQ[E(3)]
        m = W[0].to_matrix()
        self.MS = MatrixSpace(self.R, *m.dimensions())
        self.W = W
    def gens(self):
        return self.W.gens()
    def base_ring(self):
        return self.R
    def degree(self):
        return self.W.degree()
    def cardinality(self):
        return self.W.cardinality()
    def list(self):
        return [self.MS(x.to_matrix()) for x in self.W]  

# An irreducible complex reflection group
W = ReflectionGroup((2,1,3))
#W = ReflectionGroup(4)
W2 = refl_wrapper(W)
inv = inv_gens.invariant_generators(W2)







#G = DihedralGroup(4)
#H = PermutationGroup([[(1,4)],[(1,2),(3,4)]])
#H.isomorphism_to(G)
#W = ReflectionGroup(['A',2])

#gndR2 = GradedCommutativeAlgebra(QQ,'x,y')
