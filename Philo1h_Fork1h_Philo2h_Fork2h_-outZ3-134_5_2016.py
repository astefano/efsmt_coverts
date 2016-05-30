from z3 import *

def myin(s1, s2):
	for x in s1:
		if not(x in s2): 
			return False 
	print s1; print " is in "; print s2
	return True

def getII(F):
	 blockAnd = []
	 s = Solver()
	 s.add(F)
	 while True:
		 if s.check() == sat:
			 m = s.model()
			 # Create a new constraint the blocks the current model
			 block = []
			 blockOr = []
			 for d in m:
				 c = d()
				 block.append(And(Not(c), m[d]))
				 #block.append(And(c, Not(m[d])))
				 if m[d].sexpr() == 'true': 
				 	 blockOr.append(c)
			 #if block != []:		
			 #	s.add(Or(block))
			 if blockOr != []:
			         s.add(Or(block))		
				 blockAnd.append(Or(blockOr))		
		         	 print "m = ", m 		
				 print "block = ", Or(block)
		 else:
			 return And(blockAnd)


def getIIOld(F):
	 blockAnd = []
	 s = Solver()
	 s.add(F)
	 while True:
		 if s.check() == sat:
			 m = s.model()
			 # Create a new constraint the blocks the current model
			 block = []
			 blockOr = []
			 for d in m:
				 c = d()
				 block.append(c != m[d])
				 if m[d].sexpr() == 'true': 
					 blockOr.append(c)
				 # d is a declaration                                                                                                                                     
				 # create a constant from declaration
			 if block != []:		
			 	s.add(Or(block))
			 if len(blockOr) > 1: 
			 	blockAnd.append(Or(blockOr))
			 elif len(blockOr) == 1:	
			 	blockAnd.append(blockOr[0])
		 else:
			 return And(blockAnd)

def getAllModels(F, lim):
	 result = []
	 s = Solver()
	 s.add(F)
	 i = 0
	 while i < lim:
		 i = i + 1
		 if s.check() == sat:
			 m = s.model()
			 result.append(m)
			 #printModel(m)	
			 block = []
			 for d in m:
				 c = d()
				 block.append(c != m[d])
				 #if block != []:		
			 s.add(Or(block))
		 else:
			 return result

def printModels(models):
	for m in models:
		printModel(m)

def printModel(M):
	print "["
	for d in M: 
		if M[d].sexpr() != 'false':
			print "%s = %s" % (d.name(), M[d])
	print "]"

#given a formula F and a model M, return F[M]
def subst(F, M):
	r = F
	for d in M: 
		if M[d].sort().sexpr() == 'Bool':
			r = substitute(r,((Bool(d.name()), BoolVal(str(M[d])))))
		elif M[d].sort().sexpr() == 'Int':
			r = substitute(r, ((Int(d.name()), IntVal(str(M[d])))))
	return r

def getCEX(F):
    toSolve = Solver()
    toSolve.add(F)
    if toSolve.check() == sat:
        m = toSolve.model()
        printModel(m)
    else:
        print "no solution"



p11, p12, p13, p10 = Bools('p11 p12 p13 p10')
f10, f11 = Bools('f10 f11')
p21, p22, p23, p20 = Bools('p21 p22 p23 p20')
f20, f21 = Bools('f20 f21')
beta1, hreleasephio1, heatphio1, eta1, gamma1, hendphio1, t1, ts1, htakeleftphio1, alpha1 = Ints('beta1 hreleasephio1 heatphio1 eta1 gamma1 hendphio1 t1 ts1 htakeleftphio1 alpha1')
htakefork1, hreleasefork1 = Ints('htakefork1 hreleasefork1')
hreleasephio2, hendphio2, beta2, htakeleftphio2, eta2, t2, heatphio2, gamma2, ts2, alpha2 = Ints('hreleasephio2 hendphio2 beta2 htakeleftphio2 eta2 t2 heatphio2 gamma2 ts2 alpha2')
htakefork2, hreleasefork2 = Ints('htakefork2 hreleasefork2')




hreleasephio1releasefork1releasefork2, htakeleftphio2takefork2, heatphio2takefork1, htakeleftphio1takefork1, heatphio1takefork2, hendphio1endphio2, hreleasephio2releasefork2releasefork1 = Ints('hreleasephio1releasefork1releasefork2 htakeleftphio2takefork2 heatphio2takefork1 htakeleftphio1takefork1 heatphio1takefork2 hendphio1endphio2 hreleasephio2releasefork2releasefork1')

ciPhilo1h = And(Or(And(p11,  gamma1 >= hendphio1,  hendphio1 >= 0,  hendphio1 == heatphio1,  hendphio1 == ts1,  hendphio1 == hreleasephio1,  hendphio1 == t1,  hendphio1 == htakeleftphio1), And(p12,  3 >= t1,  gamma1 + t1 >= hendphio1,  hendphio1 >= t1,  t1 >= 0,  hendphio1 >= eta1 + t1,  hendphio1 == heatphio1,  hendphio1 == ts1,  hendphio1 == hreleasephio1,  t1 == htakeleftphio1), And(p13,  3 >= heatphio1,  gamma1 + htakeleftphio1 >= hendphio1,  hendphio1 >= htakeleftphio1,  heatphio1 >= 0,  heatphio1 + 3 >= htakeleftphio1,  htakeleftphio1 >= 2 + heatphio1,  hendphio1 >= eta1 + htakeleftphio1,  hendphio1 == ts1,  hendphio1 == hreleasephio1,  heatphio1 == t1), And(p10,  alpha1 >= heatphio1,  gamma1 + htakeleftphio1 >= hendphio1,  hendphio1 >= htakeleftphio1,  heatphio1 + 3 >= htakeleftphio1,  heatphio1 >= 2 + hreleasephio1,  hreleasephio1 >= 0,  hreleasephio1 + 3 >= heatphio1,  htakeleftphio1 >= 2 + heatphio1,  hendphio1 >= eta1 + htakeleftphio1,  hendphio1 == ts1,  heatphio1 == t1), And(p11,  alpha1 + hendphio1 >= heatphio1,  gamma1 >= hendphio1,  gamma1 >= eta1,  heatphio1 + 3 >= htakeleftphio1,  heatphio1 >= 2 + hreleasephio1,  hreleasephio1 >= hendphio1,  hendphio1 >= 0,  hreleasephio1 + 3 >= heatphio1,  htakeleftphio1 >= 2 + heatphio1,  gamma1 + htakeleftphio1 >= beta1 + hendphio1,  hendphio1 == ts1,  hendphio1 == t1), And(p12,  3 >= t1,  alpha1 + hendphio1 >= heatphio1,  gamma1 + t1 >= hendphio1,  hendphio1 >= t1,  heatphio1 >= 2 + hreleasephio1,  t1 >= 0,  hreleasephio1 + 3 >= heatphio1,  hreleasephio1 >= hendphio1,  hendphio1 >= eta1 + t1,  gamma1 + heatphio1 + 3 >= beta1 + hendphio1,  hendphio1 == ts1,  t1 == htakeleftphio1), And(p13,  3 >= heatphio1,  alpha1 + hendphio1 >= 2 + hreleasephio1,  alpha1 + gamma1 + 3 >= beta1,  gamma1 + htakeleftphio1 >= hendphio1,  hendphio1 >= htakeleftphio1,  heatphio1 >= 0,  heatphio1 + 3 >= htakeleftphio1,  htakeleftphio1 >= 2 + heatphio1,  hreleasephio1 >= hendphio1,  hendphio1 >= eta1 + htakeleftphio1,  gamma1 + hreleasephio1 + 6 >= beta1 + hendphio1,  hendphio1 == ts1,  heatphio1 == t1), And(p10,  alpha1 >= heatphio1,  alpha1 + gamma1 + 3 >= beta1,  gamma1 + htakeleftphio1 >= hendphio1,  hendphio1 >= htakeleftphio1,  heatphio1 + 3 >= htakeleftphio1,  heatphio1 >= 2 + hreleasephio1,  hreleasephio1 >= 0,  hreleasephio1 + 3 >= heatphio1,  htakeleftphio1 >= 2 + heatphio1,  hendphio1 >= eta1 + htakeleftphio1,  hendphio1 == ts1,  heatphio1 == t1)), Not(Or(And(p11, p12), And(p11, p13), And(p11, p10), And(p12, p13), And(p12, p10), And(p13, p10))))

ciFork1h = And(Or(And(f10,  hreleasefork1 >= 0,  htakefork1 == hreleasefork1), And(f11,  htakefork1 >= 0,  hreleasefork1 >= htakefork1), And(f10,  htakefork1 >= hreleasefork1,  hreleasefork1 >= 0)), Not(And(f10, f11)))

ciPhilo2h = And(Or(And(p21,  gamma2 >= hendphio2,  hendphio2 >= 0,  hendphio2 == ts2,  hendphio2 == t2,  hendphio2 == hreleasephio2,  hendphio2 == htakeleftphio2,  hendphio2 == heatphio2), And(p22,  4 >= t2,  gamma2 + t2 >= hendphio2,  hendphio2 >= t2,  t2 >= 0,  hendphio2 >= eta2 + t2,  hendphio2 == ts2,  hendphio2 == hreleasephio2,  t2 == htakeleftphio2,  hendphio2 == heatphio2), And(p23,  2 >= t2,  gamma2 + htakeleftphio2 >= hendphio2,  hendphio2 >= htakeleftphio2,  htakeleftphio2 >= 3 + t2,  t2 >= 0,  t2 + 4 >= htakeleftphio2,  hendphio2 >= eta2 + htakeleftphio2,  hendphio2 == ts2,  hendphio2 == hreleasephio2,  t2 == heatphio2), And(p20,  alpha2 >= t2,  gamma2 + htakeleftphio2 >= hendphio2,  hendphio2 >= htakeleftphio2,  t2 + 4 >= htakeleftphio2,  t2 >= 1 + hreleasephio2,  hreleasephio2 >= 0,  hreleasephio2 + 2 >= t2,  htakeleftphio2 >= 3 + t2,  hendphio2 >= eta2 + htakeleftphio2,  hendphio2 == ts2,  t2 == heatphio2), And(p21,  alpha2 + hendphio2 >= heatphio2,  gamma2 >= hendphio2,  gamma2 >= eta2,  hendphio2 >= 0,  hreleasephio2 + 2 >= heatphio2,  htakeleftphio2 >= 3 + heatphio2,  heatphio2 + 4 >= htakeleftphio2,  heatphio2 >= 1 + hreleasephio2,  hreleasephio2 >= hendphio2,  gamma2 + htakeleftphio2 >= beta2 + hendphio2,  hendphio2 == ts2,  hendphio2 == t2), And(p22,  4 >= t2,  alpha2 + hendphio2 >= heatphio2,  gamma2 + t2 >= hendphio2,  hendphio2 >= t2,  hreleasephio2 + 2 >= heatphio2,  t2 >= 0,  heatphio2 >= 1 + hreleasephio2,  hreleasephio2 >= hendphio2,  hendphio2 >= eta2 + t2,  gamma2 + heatphio2 + 4 >= beta2 + hendphio2,  hendphio2 == ts2,  t2 == htakeleftphio2), And(p23,  2 >= t2,  alpha2 + hendphio2 >= 1 + hreleasephio2,  alpha2 + gamma2 + 4 >= beta2,  gamma2 + htakeleftphio2 >= hendphio2,  hendphio2 >= htakeleftphio2,  htakeleftphio2 >= 3 + t2,  t2 >= 0,  t2 + 4 >= htakeleftphio2,  hreleasephio2 >= hendphio2,  hendphio2 >= eta2 + htakeleftphio2,  gamma2 + hreleasephio2 + 6 >= beta2 + hendphio2,  hendphio2 == ts2,  t2 == heatphio2), And(p20,  alpha2 >= t2,  alpha2 + gamma2 + 4 >= beta2,  gamma2 + htakeleftphio2 >= hendphio2,  hendphio2 >= htakeleftphio2,  t2 + 4 >= htakeleftphio2,  t2 >= 1 + hreleasephio2,  hreleasephio2 >= 0,  hreleasephio2 + 2 >= t2,  htakeleftphio2 >= 3 + t2,  hendphio2 >= eta2 + htakeleftphio2,  hendphio2 == ts2,  t2 == heatphio2)), Not(Or(And(p21, p22), And(p21, p23), And(p21, p20), And(p22, p23), And(p22, p20), And(p23, p20))))

ciFork2h = And(Or(And(f20,  hreleasefork2 >= 0,  htakefork2 == hreleasefork2), And(f21,  htakefork2 >= 0,  hreleasefork2 >= htakefork2), And(f20,  htakefork2 >= hreleasefork2,  hreleasefork2 >= 0)), Not(And(f20, f21)))

Kparams = And(gamma1 >= eta1, alpha1 + gamma1 + 3 >= beta1, gamma2 >= eta2, alpha2 + gamma2 + 4 >= beta2)

#abstract reach
absReachII = Or(And(p11, f10, p21, f20), And(p11, f10, p20, f20), And(p11, f11, p23, f21), And(p11, f10, p22, f21), And(p10, f10, p21, f20), And(p12, f11, p21, f20), And(p11, f10, p22, f21), And(p12, f11, p21, f20), And(p12, f11, p20, f20), And(p11, f10, p21, f20), And(p10, f10, p20, f20), And(p10, f11, p23, f21), And(p13, f11, p20, f21), And(p13, f11, p21, f21), And(p10, f10, p22, f21)) 

#Enabled guided by absReach
En = Or(Not(And(p11, f10, p21, f20, -eta1 + t1 >= 0, -t2 + gamma2 >= 0, gamma1 - t1 >= 0)), Not(And(p11, f10, p20, f20, -eta1 + t1 >= 0, -t2 + alpha2 >= 0, gamma1 - t1 >= 0)), Not(And(p11, f11, p23, f21, gamma1 - t1 >= 0, -t2 + alpha2 >= 0, -t2 >= -2)), Not(And(p11, f10, p22, f21, gamma1 - t1 >= 0, -t2 >= -4)), Not(And(p10, f10, p21, f20, -eta2 + t2 >= 0, -t1 + alpha1 >= 0, -t2 + gamma2 >= 0)), Not(And(p12, f11, p21, f20, -t2 + gamma2 >= 0, -t1 >= -3)), Not(And(p11, f10, p22, f21, -eta1 + t1 >= 0, gamma1 - t1 >= 0, -t2 >= -4)), Not(And(p12, f11, p21, f20, -eta2 + t2 >= 0, -t2 + gamma2 >= 0, -t1 >= -3)), Not(And(p12, f11, p20, f20, -t2 + alpha2 >= 0, -t1 >= -3)), Not(And(p11, f10, p21, f20, -eta2 + t2 >= 0, -t2 + gamma2 >= 0, gamma1 - t1 >= 0)), Not(And(p10, f10, p20, f20, -beta1 + ts1 >= 0, -beta2 + ts2 >= 0, -t1 + alpha1 >= 0, -t2 + alpha2 >= 0)), Not(And(p10, f11, p23, f21, -t2 + alpha2 >= 0, -t1 + alpha1 >= 0, -t2 >= -2)), Not(And(p13, f11, p20, f21, -t2 + alpha2 >= 0, -t1 + alpha1 >= 0, -t1 >= -3)), Not(And(p13, f11, p21, f21, -t2 + gamma2 >= 0, -t1 + alpha1 >= 0, -t1 >= -3)), Not(And(p10, f10, p22, f21, -t1 + alpha1 >= 0, -t2 >= -4)))

DisN = Not(En)
Safe = t1 + t2 <= 60

EqsS = And(And(And(hendphio1 == hendphio2, Or(And(heatphio2 == htakefork1, heatphio2 <= htakeleftphio1), And(htakeleftphio1 == htakefork1, htakeleftphio1 <= heatphio2))), Or(And(htakeleftphio2 == htakefork2, htakeleftphio2 <= heatphio1), And(heatphio1 == htakefork2, heatphio1 <= htakeleftphio2))), Or(And(And(hreleasephio1 == hreleasefork1, hreleasephio1 == hreleasefork2, hreleasefork1 == hreleasefork2), hreleasephio1 <= hreleasephio2), And(And(hreleasephio2 == hreleasefork2, hreleasephio2 == hreleasefork1, hreleasefork2 == hreleasefork1), hreleasephio2 <= hreleasephio1)))
NewCond = True
Gih = And(ciPhilo1h, ciFork1h, ciPhilo2h, ciFork2h, EqsS, absReachII, NewCond)
dead = And(Gih, DisN)
EqsC = And(Or(And(htakefork1 == htakeleftphio1takefork1, htakeleftphio1takefork1 <= heatphio2takefork1), And(htakefork1 == heatphio2takefork1, heatphio2takefork1 <= htakeleftphio1takefork1)), Or(And(hreleasefork1 == hreleasephio1releasefork1releasefork2, hreleasephio1releasefork1releasefork2 <= hreleasephio2releasefork2releasefork1), And(hreleasefork1 == hreleasephio2releasefork2releasefork1, hreleasephio2releasefork2releasefork1 <= hreleasephio1releasefork1releasefork2)), hreleasephio2 == hreleasephio2releasefork2releasefork1, Or(And(hreleasefork2 == hreleasephio1releasefork1releasefork2, hreleasephio1releasefork1releasefork2 <= hreleasephio2releasefork2releasefork1), And(hreleasefork2 == hreleasephio2releasefork2releasefork1, hreleasephio2releasefork2releasefork1 <= hreleasephio1releasefork1releasefork2)), htakeleftphio2 == htakeleftphio2takefork2, heatphio1 == heatphio1takefork2, hendphio2 == hendphio1endphio2, heatphio2 == heatphio2takefork1, Or(And(htakefork2 == htakeleftphio2takefork2, htakeleftphio2takefork2 <= heatphio1takefork2), And(htakefork2 == heatphio1takefork2, heatphio1takefork2 <= htakeleftphio2takefork2)), htakeleftphio1 == htakeleftphio1takefork1, hendphio1 == hendphio1endphio2, hreleasephio1 == hreleasephio1releasefork1releasefork2)
Sep = And(Or(htakeleftphio2takefork2 - heatphio1takefork2 >= 0, heatphio1takefork2 - htakeleftphio2takefork2 >= 0), Or(hreleasephio1releasefork1releasefork2 - hreleasephio2releasefork2releasefork1 >= 0, hreleasephio2releasefork2releasefork1 - hreleasephio1releasefork1releasefork2 >= 0), Or(htakeleftphio1takefork1 - heatphio2takefork1 >= 0, heatphio2takefork1 - htakeleftphio1takefork1 >= 0))
GihExt = And(ciPhilo1h, ciFork1h, ciPhilo2h, ciFork2h, EqsS, EqsC, Sep, absReachII, NewCond)
deadExt = And(GihExt, DisN)
print "Solving deadExt:" 
getCEX(deadExt)

getSubst = And(GihExt, Safe)
print "getSubst:" 
getCEX(getSubst)

Params = And(beta1 >= 0, eta1 >= 0, gamma1 >= 0, alpha1 >= 0, eta2 >= 0, beta2 >= 0, gamma2 >= 0, alpha2 >= 0)
PosClks = And(hreleasephio1 >= 0, heatphio1 >= 0, hendphio1 >= 0, t1 >= 0, ts1 >= 0, htakeleftphio1 >= 0, hreleasephio2 >= 0, hendphio2 >= 0, htakeleftphio2 >= 0, t2 >= 0, heatphio2 >= 0, ts2 >= 0, htakefork2 >= 0, hreleasefork2 >= 0, hreleasephio1releasefork1releasefork2 >= 0, htakeleftphio2takefork2 >= 0, heatphio2takefork1 >= 0, htakeleftphio1takefork1 >= 0, heatphio1takefork2 >= 0, hendphio1endphio2 >= 0, hreleasephio2releasefork2releasefork1 >= 0)

EFformula = Exists([], And(Kparams, Params, ForAll([c20, c21, c10, c11, y, x, hb, hc, ha1, ha2, s10, s11, s12, s20, s21, s22], Implies(And(PosClks, Gih), And(En, safe)))))
s = Solver() 
s.add(EFformula) 
print s.check() 
print s.model()

