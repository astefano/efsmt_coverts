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



lc0, lc1 = Bools('lc0 lc1')
l0_0, l1_0 = Bools('l0_0 l1_0')
xc, p, hcoolc, hrestc = Ints('xc p hcoolc hrestc')
hrest_0, x_0, hcool_0, ct = Ints('hrest_0 x_0 hcool_0 ct')



cicontrollerhh = Or(And(lc0,  900 >= xc,  xc >= 0,  xc == hcoolc,  xc == hrestc), And(lc1,  450 >= xc,  xc >= 0,  xc == hcoolc,  xc + 900 == hrestc), And(lc0,  900 >= xc,  xc >= 0,  xc + 450 == hcoolc,  xc == hrestc))

NotAt2Locs_controllerhh  = Not(And(lc0, lc1))

Kp_controllerhh = And(Tactic('qe2').apply(Exists([xc,hcoolc,hrestc], And( 900 >= xc, xc >= 0, xc == hcoolc, xc == hrestc))).as_expr(), Tactic('qe2').apply(Exists([xc,hcoolc,hrestc], And( 450 >= xc, xc >= 0, xc == hcoolc, xc + 900 == hrestc))).as_expr())

ciRod_0hh = Or(And(l0_0,  hrest_0 >= 0,  x_0 == hrest_0,  hcool_0 == hrest_0), And(l1_0,  x_0 >= hcool_0,  hcool_0 >= 0,  x_0 >= ct + hcool_0,  x_0 == hrest_0), And(l0_0,  hcool_0 >= hrest_0,  hrest_0 >= 0,  x_0 == hrest_0))

NotAt2Locs_Rod_0hh  = Not(And(l0_0, l1_0))

Kp_Rod_0hh = And(Tactic('qe2').apply(Exists([x_0,hcool_0,hrest_0], And( hrest_0 >= 0, x_0 == hrest_0, hcool_0 == hrest_0))).as_expr(), Tactic('qe2').apply(Exists([x_0,hcool_0,hrest_0], And( x_0 >= hcool_0, hcool_0 >= 0, x_0 >= ct + hcool_0, x_0 == hrest_0))).as_expr())


#abstract reach
absReachII = Or(And(lc0, l0_0), And(lc1, l1_0)) 

#Enabled guided by absReach
En = Or(And(lc0, l0_0, -xc >= -900, -ct + x_0 >= 0), And(lc1, l1_0, -xc >= -450))

DisN = Not(En)

NewCond = True
NotAt2Locs_all = And(NotAt2Locs_controllerhh, NotAt2Locs_Rod_0hh)
PosClks = And(xc >= 0, p >= 0, hcoolc >= 0, hrestc >= 0, hrest_0 >= 0, x_0 >= 0, hcool_0 >= 0, ct >= 0)
Kp_all = And(Kp_controllerhh, Kp_Rod_0hh)
AddInvs = And(absReachII, NewCond, PosClks, NotAt2Locs_all)
Gi = And(cicontrollerhh, ciRod_0hh, AddInvs)

hcoolccool_0, hrestcrest_0 = Ints('hcoolccool_0 hrestcrest_0')
PosHClks = And(hcoolccool_0 >= 0, hrestcrest_0 >= 0)
EqsS = And(hrestc == hrest_0, hcoolc == hcool_0)
Gih = And(cicontrollerhh, ciRod_0hh, EqsS, AddInvs, PosHClks )
dead = And(Gih, DisN)
EqsC = And(hcoolc == hcoolccool_0, hcool_0 == hcoolccool_0, hrestc == hrestcrest_0, hrest_0 == hrestcrest_0)
Sep = True
GihExt = And(cicontrollerhh, ciRod_0hh, EqsS, EqsC, Sep, AddInvs )
deadExt = And(GihExt, DisN)
print "Solving deadExt:" 
getCEX(deadExt)



safe = True
#Solving EF formula: 
EFformula = Exists([p,ct], And(Kp_all, ForAll([lc0, lc1, l0_0, l1_0, hrestc, hcool_0, hcoolc, xc, x_0, hrest_0, hcoolccool_0, hrestcrest_0], Implies(Gih, And(safe, En)))))
s = Solver() 
s.add(EFformula) 
print s.check() 
print s.model()