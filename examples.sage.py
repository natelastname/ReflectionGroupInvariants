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
       - hyp_vars, a list of variables u_i corresponding to hyperplanes.
Outputs:
       - A matrix (the action of g on the u_i induced by the action of g on x_i)
'''
def get_action(g, HT, hyp_vars):

    rep = g.representative().matrix()
    mat = []

    hyp_roots = [var.substitute(HT) for var in hyp_vars]

    # g is a conjugacy class representative
    # we have to compute the action of g on the hyperplanes "hyp"
    for i in range(0,len(hyp_vars)):
        hyp = hyp_vars[i].substitute(HT)
        act = rep.act_on_polynomial(hyp)
        #print("%s -> %s"%(hyp_vars[i], act))
        found = []
        found_index = 0
        ent = 0
        # find the root that has the same solution set as "act"
        for j in range(0,len(hyp_roots)):
            root = hyp_roots[j]
            if act/act.lc() == root/root.lc():
                ent = root.lc()/act.lc()
                found_index = j
                found.append(root)
        
        assert(len(found) == 1)        
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
    print("----- computing Orlik-Artin ideal: -----")
    (I, HT) = refl.orlik_artin_ideal(W)
    #tests_refl.test_gens_OA(I, HT)
    print("----- variables of Orlik-Artin algebra: -----")
    varsI = HT.keys()
    varsI.sort()
    for i in range(0, len(varsI)):
        A = varsI[i]
        B = HT[varsI[i]].to_symmetric_space()
        #print("%s: %s"%(A, B))

    print("----- Generators of Orlik-Artin ideal: -----")
    gensI = I.gens()
    for i in range(0, len(gensI)):
        A = i
        B = gensI[i]
        
    print("----- computing GB of Orlik-Artin ideal... -----")
    I = I.groebner_basis()
    print("----- computing normal basis of quotient ring... -----")
    gndR = I[0].parent()
    quot = gndR.quotient(I)
    B = Ideal(I).normal_basis()
    Bdeg = refl.sort_by_degree(B)
    
    i = 0
    print("----- K-basis for the quotient ring sorted by degree: -----")
    for x in Bdeg:
        print(str(i)+": "+str(x))
        i = i + 1

    MG_rep = MG.conjugacy_classes()
    HT = hyperplanes_to_linear_polys(HT)

    char_table = MG.character_table()
    char_table = [list(char_table[i]) for i in range(0,char_table.nrows())]

    print("----------- Action of MG on the graded components of quot: -----------")
    for deg in Bdeg:
        rep = []
        for g in MG_rep:
            act = get_action(g, HT, gndR.gens())
            res = refl.matrix_wrt_standard_monos(deg, quot, act)        
            rep.append(res)
        char = []
        for mat in rep:
            char.append(mat.trace())
        CF = ClassFunction(MG, char)
        print("--------- action of MG on "+str(deg)+":")
        CF_decomp = CF.decompose()
        for comp in CF_decomp:
            vals = list(comp[1].values())
            #print(vals)
            print("#%s, dimension:%s"%(char_table.index(vals),vals[0]))
            
    #print("---- MG.character_table(): ----")
    #print(char_table)
            
print("---------------------------------")
print("ReflectionGroup(4):")
print("---------------------------------")
W = ReflectionGroup(4)
(MG, MS) = refl.to_matrix_gp(W)
run_example(W,MG)

