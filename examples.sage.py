import refl_invariants as refl
import tests_refl
from matrix_gps_local import finitely_generated as fin_gen

import pdb

reload(refl)
reload(tests_refl)
reload(fin_gen)

'''
Inputs: 
       - g, a matrix that acts on the variables of the hyperplanes in HT.
       - HT, a hashtable that maps the variables u_i in hyp_vars to linear polys.
       - HT_inv, maps the values of HT to their keys.
       - hyp_vars, a list of variables u_i corresponding to hyperplanes.
Outputs:
       - A matrix (the action of g on the u_i induced by the action of g on x_i)
'''
def get_action(g, HT, hyp_vars):

    rep = g.representative().matrix()
    mat = []

    hyp_roots = [var.substitute(HT) for var in hyp_vars]
    
    for i in range(0,len(hyp_vars)):
        hyp = hyp_vars[i].substitute(HT)
        act = rep.act_on_polynomial(hyp)
        
        found = []
        found_index = 0
        # find the root that has the same solution set as "act"
        for j in range(0,len(hyp_roots)):
            root = hyp_roots[j]
            if act/(act.lc()) == root/(root.lc()):
                found.append(root)
                ent = act.lc()/root.lc()
                found_index = j
                
        assert(len(found) == 1)
        #print("%s -> %s"%(hyp_vars[i], act))

        col = [0 for foo in hyp_vars]
        col[found_index] = ent
        mat.append(col)

    return matrix(rep.base_ring(), mat)

def hyperplanes_to_linear_polys(HT):
    # HT maps the variables u_i to hyperplanes
    HT2 = {}
    elt = 0
    for key in HT.keys():
        elt = key
        HT2[key] = HT[key].to_symmetric_space()

    return HT2
    
def run_example(W,MG):
    print("computing Orlik-Artin ideal:")
    (I, HT) = refl.orlik_artin_ideal(W)
    print("computing GB of Orlik-Artin ideal...")
    I = I.groebner_basis()
    print("computing normal basis of quotient ring...")
    gndR = I[0].parent()
    quot = gndR.quotient(I)
    B = Ideal(I).normal_basis()
    Bdeg = refl.sort_by_degree(B)
    
    i = 0
    print("K-basis for the quotient ring sorted by degree:")
    for x in Bdeg:
        print(str(i)+": "+str(x))
        i = i + 1

    MG_rep = MG.conjugacy_classes()
    HT = hyperplanes_to_linear_polys(HT)
    
    print("----------- Action of MG on the graded components of quot: -----------")
    for deg in Bdeg:
        rep = []
        for g in MG_rep:
            #print("------------------------------------")
            #print("-------- conjugacy class representative:")
            #print(g.representative())
            act = get_action(g, HT, gndR.gens())
            res = refl.matrix_wrt_standard_monos(deg, quot, act)        
            #print("action on standard monos:")
            #print(res)
            rep.append(res)
        print("--------- action of MG on "+str(deg)+":")
        char = []
        for mat in rep:
            char.append(mat.trace())
        CF = ClassFunction(MG, char)
        for comp in CF.decompose():
            #print("%s*%s"%(comp[0],comp[1].values()))
            print("%s"%(comp[1].values()))

    print("---- MG.character_table(): ----")
    print(MG.character_table())
            
print("---------------------------------")
print("ReflectionGroup(4):")
print("---------------------------------")
W = ReflectionGroup(4)
                
assert(W.cardinality() == len(W.roots()))
(MG, MS) = refl.to_matrix_gp(W)
run_example(W,MG)


