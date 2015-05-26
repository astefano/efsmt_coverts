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


hcoolcool0, hcoolcool1, hheatrest0, hheatrest1 = Ints('hcoolcool0 hcoolcool1 hheatrest0 hheatrest1')


lc2 = Bool('lc2')

hcool0 = Int('hcool0')

l10 = Bool('l10')

lc3 = Bool('lc3')

lc1 = Bool('lc1')

l11 = Bool('l11')

t0 = Int('t0')

hheat = Int('hheat')

M = Int('M')

vr1 = Int('vr1')

t1 = Int('t1')

m = Int('m')

T = Int('T')

hrest0 = Int('hrest0')

t = Int('t')

vr0 = Int('vr0')

hcool1 = Int('hcool1')

hcool = Int('hcool')

l21 = Bool('l21')

hrest1 = Int('hrest1')

l20 = Bool('l20')



InvtcAllHist = Or(And(lc1, l10, l11,  6*hheat > t,  t >= 0,  6*hcool1 > t,  6*hrest1 > t,  m == 3,  M == 15,  T == 6,  t == 6*hcool,  t + 36 == 6*t0,  t == 6*hcool0,  t == 6*hrest0,  t + 36 == 6*t1), And(lc2, l20, l11,  t + 2*hheat > 20,  15 >= t,  t + 2*hcool1 > 20,  t + 2*hrest1 > 20,  m == 3,  M == 15,  T == 6,  t + 2*hcool == 15,  t + 2*t0 == 32,  t + 2*hcool0 == 15,  t + 2*hrest0 == 20,  t + 2*t1 == 32), And(lc3, l10, l21,  t + 2*hheat > 20,  15 >= t,  t + 2*hrest1 > 20,  m == 3,  M == 15,  T == 6,  t + 2*hcool == 15,  t + 2*t0 == 32,  t + 2*hcool0 == 20,  t + 2*hrest0 == 20,  t + 2*t1 == 32,  t + 2*hcool1 == 15), And(lc1, l10, l11,  t >= 3,  6*hcool1 > 48 + t,  6*hrest1 > 48 + t,  m == 3,  M == 15,  T == 6,  t == 3 + 6*hheat,  t + 33 == 6*hcool,  t == 3 + 6*t0,  t + 33 == 6*hcool0,  t == 3 + 6*hrest0,  t + 84 == 6*t1), And(lc1, l10, l11,  t >= 3,  m == 3,  M == 15,  T == 6,  t == 3 + 6*hheat,  t + 33 == 6*hcool,  t + 84 == 6*t0,  t + 48 == 6*hcool0,  t + 48 == 6*hrest0,  t == 3 + 6*t1,  t + 33 == 6*hcool1,  t == 3 + 6*hrest1), And(lc3, l10, l21,  15 >= t,  t + 2*hrest1 > 36,  m == 3,  M == 15,  T == 6,  t + 2*hheat == 19,  t + 2*hcool == 15,  t + 2*t0 == 19,  t + 2*hcool0 == 31,  t + 2*hrest0 == 19,  t + 2*t1 == 48,  t + 2*hcool1 == 15), And(lc2, l20, l11,  15 >= t,  m == 3,  M == 15,  T == 6,  t + 2*hheat == 19,  t + 2*hcool == 15,  t + 2*t0 == 48,  t + 2*hcool0 == 15,  t + 2*hrest0 == 36,  t + 2*t1 == 19,  t + 2*hcool1 == 31,  t + 2*hrest1 == 19), And(lc1, l10, l11,  t >= 3,  m == 3,  M == 15,  T == 6,  t == 3 + 6*hheat,  t + 33 == 6*hcool,  t + 45 == 6*t0,  t + 81 == 6*hcool0,  t + 45 == 6*hrest0,  t == 3 + 6*t1,  t + 33 == 6*hcool1,  t == 3 + 6*hrest1), And(lc1, l10, l11,  t >= 3,  m == 3,  M == 15,  T == 6,  t == 3 + 6*hheat,  t + 33 == 6*hcool,  t == 3 + 6*t0,  t + 33 == 6*hcool0,  t == 3 + 6*hrest0,  t + 45 == 6*t1,  t + 81 == 6*hcool1,  t + 45 == 6*hrest1), And(lc2, l20, l11,  15 >= t,  m == 3,  M == 15,  T == 6,  t + 2*hheat == 19,  t + 2*hcool == 15,  t + 2*t0 == 35,  t + 2*hcool0 == 15,  t + 2*hrest0 == 35,  t + 2*t1 == 19,  t + 2*hcool1 == 31,  t + 2*hrest1 == 19), And(lc3, l10, l21,  15 >= t,  m == 3,  M == 15,  T == 6,  t + 2*hheat == 19,  t + 2*hcool == 15,  t + 2*t0 == 19,  t + 2*hcool0 == 31,  t + 2*hrest0 == 19,  t + 2*t1 == 35,  t + 2*hcool1 == 15,  t + 2*hrest1 == 35))
not2Locs = Not(Or(And(lc1, lc2), And(l10, l20), And(l11, l21)))
DisN = And(not2Locs, t == M, t0 < T, t1 < T, t0 >= 0, t1 >= 0)

EqsS = And(Or(And(hheat == hrest0, hheat <= hrest1), And(hheat == hrest1, hheat <= hrest0)), Or(And(hcool == hcool0, hcool <= hcool1), And(hcool == hcool1, hcool <= hcool0)))
Gih = And(InvtcAllHist, EqsS)
dead = And(Gih, DisN)
EqsC = And(Or(And(hcool == hcoolcool0, hcoolcool0 <= hcoolcool1), And(hcool == hcoolcool1, hcoolcool1 <= hcoolcool0)), hcool1 == hcoolcool1, Or(And(hheat == hheatrest0, hheatrest0 <= hheatrest1), And(hheat == hheatrest1, hheatrest1 <= hheatrest0)), hcool0 == hcoolcool0, hrest0 == hheatrest0, hrest1 == hheatrest1)
Sep = And(Or(hcoolcool0 - hcoolcool1 >= 0, hcoolcool1 - hcoolcool0 >= 0), Or(hheatrest0 - hheatrest1 >= 0, hheatrest1 - hheatrest0 >= 0))
GihExt = And(InvtcAllHist, EqsS, EqsC, Sep)
deadExt = And(GihExt, DisN)
print "Solving deadExt:" 
getCEX(deadExt)

allpos = And(hcoolcool0 >= 0, hcoolcool1 >= 0, hheatrest0 >= 0, hheatrest1 >= 0, hheat >= 0, hcool >= 0, hcool0 >= 0, hcool1 >= 0, hrest0 >= 0, hrest1 >= 0)
#SeptoShow = And(Or(hcoolcool0 - hcoolcool1 >= M, hcoolcool1 - hcoolcool0 >= M), Or(hheatrest0 - hheatrest1 >= m+M, hheatrest1 - hheatrest0 >= m+M))
SeptoShow1 = Or(hcoolcool0 - hcoolcool1 >= T, hcoolcool1	 - hcoolcool0 >= T)
SeptoShow2 = Or(hheatrest0 - hheatrest1 >= T, hheatrest1 - hheatrest0 >= T)
getCEX(And(InvtcAllHist, EqsS, EqsC, t>0, not2Locs, allpos, Not(SeptoShow2)))
