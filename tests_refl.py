'''
Inputs: 
       - poly, a polynomial.
Output:
       - A set of variables appearing in some monomial of poly.
'''
def supp(poly):
    gndR = poly.parent()
    G = gndR.gens()
    exps = poly.exponents()
    supp_poly = set([])
    for i in range(0,len(exps)):
        exp = exps[i]
        mono_supp = []
        for j in range(0,len(exp)):
            if exp[j] != 0:
                mono_supp.append(G[j])
        supp_poly = supp_poly.union(set(mono_supp))
    return supp_poly

def test_gen_OA(gen, HT):
    p = 0
    suppGen = supp(gen)
    for mono in gen.monomials():
        var = list(suppGen - supp(mono))
        assert(len(var) == 1)
        var = var[0]
        p = p + ((HT[var])*gen.monomial_coefficient(mono))

    assert(p == 0)
    #print(str(gen)+" -> pass")

# Test the result of orlik_artin_ideal.
def test_gens_OA(I, HT):
    print("--------- testing Orlik-Artin ideal: -----------")
    for gen in I.gens():
        if len(gen.monomials()) == 1:
            # It's one of the generators of the form u_i^2.
            #print(str(gen)+" -> pass")
            pass
        else:
            test_gen_OA(gen, HT)
