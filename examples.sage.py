import refl_invariants as refl
import tests_refl
from matrix_gps_local import finitely_generated as fin_gen

reload(refl)
reload(tests_refl)
reload(fin_gen)

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
    Bdeg = refl.sort_by_degree(B)
    
    i = 0
    print("K-basis for the quotient ring sorted by degree:")
    for x in Bdeg:
        print(str(i)+": "+str(x))
        i = i + 1

    # Is this guarenteed to be in the same order as the character table?
    MG_rep = MG.conjugacy_classes()

    print("Action of MG on the graded components of quot:")
    for b in Bdeg:
        rep = [refl.matrix_wrt_standard_monos(b, quot, g.representative()) for g in MG_rep]
        print("--------- action of MG on "+str(b)+":")
        char = []
        for mat in rep:
            char.append(mat.trace())
        CF = ClassFunction(MG, char)
        for comp in CF.decompose():
            print("%s*%s"%(comp[0],comp[1].values()))
    

    
            
print("---------------------------------")
print("ReflectionGroup((1,1,4)):")
print("---------------------------------")
W = ReflectionGroup((4,4,2))
(MG, MS) = refl.to_matrix_gp(W)
run_example(MG)
(I, HT) = refl.orlik_artin_ideal(W)
tests_refl.test_gens_OA(I, HT)

print("---------------------------------")
print("ReflectionGroup(4):")
print("---------------------------------")
W = ReflectionGroup(4)
(MG, MS) = refl.to_matrix_gp(W)
run_example(MG)
(I, HT) = refl.orlik_artin_ideal(W)
tests_refl.test_gens_OA(I, HT)
