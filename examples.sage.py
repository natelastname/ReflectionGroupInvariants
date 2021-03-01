import refl_invariants as refl
import tests_refl
from matrix_gps_local import finitely_generated as fin_gen

reload(refl)
reload(tests_refl)
reload(fin_gen)

def convert_hyp(gndRJ, hyp):
    g1 = gndRJ.gens()
    g2 = hyp.parent().basis()
    HT = {}
    for i in g2.keys():
        if type(i) == type(1):
            HT[g2[i]] = g1[i]
        elif type(i) == type("foo"):
            HT[i] = 1
    
    return HT

def normalize_lc(poly):

    return poly/(poly.lc())
    
    coef = poly.lc().conjugate() * poly.lc()
    coef = sqrt(coef)
    poly_norm = poly/coef
    
    assert(type(poly) == type(poly_norm))
    assert( norm(poly_norm.lc()) ==1)
    return poly_norm


def get_action(g, HT2, HT3, hyp_vars):
    rep = g.representative().matrix()
    mat = []
    for i in range(0,len(hyp_vars)):
        poly = hyp_vars[i].substitute(HT2)
        g0 = rep.act_on_polynomial(poly)
        #gg = normalize_lc(g0)
        assert(g0 in HT3)
        # The sign might be wrong
        if -gg in HT3:
            gg = -gg
            
        ent = (g0.lc())/(gg.lc())
        assert(ent * gg.lc() == g0.lc())
        out = HT3[gg]
        #print(str(hyp_vars[i])+" -> ("+str(ent)+")*"+str(out))
        col = [0 for foo in hyp_vars]
        col[hyp_vars.index(out)] = ent
        mat.append(col)
        
    return matrix(rep.base_ring(), mat)
    
    
def run_example(MG):
    print("Computing invariants...")
    G = MG.invariant_generators()
    print("computing GB...")
    J = ideal(G).groebner_basis()
    gndRJ= J[0].parent()
    print("computing Orlik-Artin ideal:")
    (I, HT) = refl.orlik_artin_ideal(W)
    for key in HT.keys():
        coefs = HT[key].coefficients()
        terms = []
        for i in range(1, len(gndRJ.gens())+1):
            terms.append(gndRJ.gens()[i-1]*coefs[i])
        print("%s -> %s"%(key, sum(terms)))
        
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

    # Is this guarenteed to be in the same order as the character table?
    MG_rep = MG.conjugacy_classes()
        
    # HT maps the variables u_i to hyperplanes
    # HT2 maps the variables u_i to linear polynomials
    HT2 = {}
    HT3 = {}
    for key in HT.keys():
        coefs = HT[key].coefficients()
        terms = []
        for i in range(1, len(gndRJ.gens())+1):
            terms.append(gndRJ.gens()[i-1]*coefs[i])

        poly = normalize_lc(sum(terms))

        HT2[key] = poly
        HT3[poly] = key
    
    print("----------- Action of MG on the graded components of quot: -----------")
    for deg in Bdeg:
        rep = []
        for g in MG_rep:
            #res = refl.matrix_wrt_standard_monos(deg, quot, g.representative().matrix())        
            act = get_action(g, HT2, HT3, gndR.gens())
            #print("---------------------------------------------------------------")
            #print(g.representative().matrix())
            #print("---------------------")
            #print(act)
            res = refl.matrix_wrt_standard_monos(deg, quot, act)        
            rep.append(res)

        print("--------- action of MG on "+str(deg)+":")
        char = []
        for mat in rep:
            char.append(mat.trace())
        CF = ClassFunction(MG, char)
        for comp in CF.decompose():
            #print("%s*%s"%(comp[0],comp[1].values()))
            print("%s"%(comp[1].values()))

    return
    print("----------- character table of MG: -----------")
    for row in MG.character_table():
        print(row)
            


'''
print("---------------------------------")
print("ReflectionGroup((4,4,2)):")
print("---------------------------------")
W = ReflectionGroup((4,4,2))
(MG, MS) = refl.to_matrix_gp(W)
run_example(MG)
(I, HT) = refl.orlik_artin_ideal(W)
tests_refl.test_gens_OA(I, HT)
'''

print("---------------------------------")
print("ReflectionGroup(4):")
print("---------------------------------")
W = ReflectionGroup(4)
(MG, MS) = refl.to_matrix_gp(W)
run_example(MG)
#(I, HT) = refl.orlik_artin_ideal(W)
#tests_refl.test_gens_OA(I, HT)
