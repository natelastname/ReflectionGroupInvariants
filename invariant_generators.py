from sage.all import *

'''
This is the "invariant_generators" method of the class "sage.groups.matrix_gps.finitely_generated.
FinitelyGeneratedMatrixGroup_gap". For whatever reason, this works when you give it an instance of
the type "sage.groups.matrix_gps.coxeter_group.CoxeterMatrixGroup_with_category". Source of this
function: 

https://github.com/sagemath/sage/blob/c4a802d2b6cb571a8a412f58d5b60250bd2a1945/src/sage/groups/matrix_gps/finitely_generated.py
'''
def invariant_generators(self):
    from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
    from sage.interfaces.singular import singular

    generated_prog = ""
    def eval_singular(code):
        print(code)
        result = singular.eval(code)
        if result != "":
            print("==>"+str(result).replace("\n","\n==>"))

        return result
    
    gens = self.gens()
    singular.LIB("finvar.lib")
    n = self.degree() 
    F = self.base_ring()
    q = F.characteristic()
    # test if the field is admissible
    if F.gen() == 1:
        # we got the rationals or GF(prime)
        FieldStr = str(F.characteristic())
    elif hasattr(F,'polynomial'):
        # we got an algebraic extension
        if len(F.gens()) > 1:
            raise NotImplementedError("can only deal with finite fields and (simple algebraic extensions of) the rationals")
        FieldStr = '(%d,%s)' % (F.characteristic(), str(F.gen()))
    else:
        # we have a transcendental extension
        FieldStr = '(%d,%s)' % (F.characteristic(),
                                ','.join(str(p) for p in F.gens()))

    # Setting Singular's variable names
    # We need to make sure that field generator and variables get different names.
    if str(F.gen())[0] == 'x':
        VarStr = 'y'
    else:
        VarStr = 'x'
    VarNames = '(' + ','.join((VarStr+str(i) for i in range(1, n+1)))+')'

    # The function call and affectation below have side-effects. Do not remove!
    # (even if pyflakes say so)
    R = singular.ring(FieldStr, VarNames, 'dp')
    if hasattr(F, 'polynomial') and F.gen() != 1:
        # we have to define minpoly
        eval_singular('minpoly = '+str(F.polynomial()).replace('x',str(F.gen())))

    # does .replace("E","rootofUnity") have potential to break something?
    A = [singular.matrix(n,n,str((x.matrix()).list()).replace("E","rootofUnity")) for x in gens]
    Lgens = ','.join((x.name() for x in A))
    PR = PolynomialRing(F, n, [VarStr+str(i) for i in range(1,n+1)])

    # Not sure about the purpose of this second condition. It has something to do with the fact
    # that 1/|G| is zero in the case that the characteristic of the field divides |G|.
    if q == 0 or (q > 0 and self.cardinality() % q):
        from sage.all import Matrix

        elements = []
        for g in self.list():
            if hasattr(g, "matrix"):
                elements.append(g.matrix())
            else:
                elements.append(g)

        
        if elements is not None:
            ReyName = 't'+singular._next_var_name()
            eval_singular('matrix %s[%d][%d]' % (ReyName,
                                                 self.cardinality(), n))
            for i in range(1,self.cardinality()+1):
                M = Matrix(F, elements[i-1])
                # In order to input a matrix into singular, we have to convert it to a sparse format.
                D = [{} for foobar in range(self.degree())]
                for x,y in M.dict().items():
                    D[x[0]][x[1]] = y
                # D is now a list of dictionaries. Each dictionary corresponds to a row of M, and contains
                # an entry for each non-zero position of that row.
                for row in range(self.degree()):
                    for t in D[row].items():
                        eval_singular('%s[%d,%d]=%s[%d,%d]+(%s)*var(%d)'
                                      % (ReyName,i,row+1,ReyName,i,row+1, repr(t[1]),t[0]+1))

            IRName = 't'+singular._next_var_name()
            eval_singular('matrix %s = invariant_algebra_reynolds(%s,1)' % (IRName,ReyName))

        else:
            ReyName = 't'+singular._next_var_name()
            eval_singular('list %s=group_reynolds((%s))' % (ReyName, Lgens))
            IRName = 't'+singular._next_var_name()
            eval_singular('matrix %s = invariant_algebra_reynolds(%s[1])' % (IRName, ReyName))

        OUT = [eval_singular(IRName+'[1,%d]' % (j))
               for j in range(1, 1+int(singular('ncols('+IRName+')')))]
        return [PR(gen) for gen in OUT]
    if self.cardinality() % q == 0:
        PName = 't' + singular._next_var_name()
        SName = 't' + singular._next_var_name()
        eval_singular('matrix %s,%s=invariant_ring(%s)' % (PName, SName, Lgens))
        OUT = [eval_singular(PName+'[1,%d]' % (j))
               for j in range(1,1+singular('ncols('+PName+')'))]
        OUT += [eval_singular(SName+'[1,%d]' % (j))
                for j in range(2,1+singular('ncols('+SName+')'))]
        return [PR(gen) for gen in OUT]
