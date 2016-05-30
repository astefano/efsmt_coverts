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


hcool0 = Int('hcool0')

l10 = Bool('l10')

t0 = Int('t0')

hrest0 = Int('hrest0')

l20 = Bool('l20')


Invrod0 = And(Or(And(l10,  t0 == 1800 + hrest0,  hcool0 == hrest0), And(l20,  hrest0 >= hcool0,  t0 == 1800 + hrest0), And(l10,  hrest0 >= 0,  t0 == hrest0), And(l20,  hrest0 >= 1800 + hcool0,  t0 == hrest0)), Not(And(l10, l20)))

lc2 = Bool('lc2')

lc1 = Bool('lc1')

hheat = Int('hheat')

vr1 = Int('vr1')

t = Int('t')

vr0 = Int('vr0')

hcool = Int('hcool')


Invcontroller = And(Or(And(lc1,  t >= 0,  t == hcool,  t == hheat), And(lc2,  t + hheat >= 900,  900 >= t,  1800 >= t + hheat,  t + hcool == 900), And(lc1,  hcool + 450 >= t,  t >= 450,  t >= hcool,  t == 450 + hheat), And(lc2,  t + hheat >= 900,  900 >= t,  1350 >= t + hheat,  t + hcool == 900)), Not(And(lc1, lc2)))


l11 = Bool('l11')

t1 = Int('t1')

hcool1 = Int('hcool1')

l21 = Bool('l21')

hrest1 = Int('hrest1')


Invrod1 = And(Or(And(l11,  t1 == 1800 + hrest1,  hcool1 == hrest1), And(l21,  hrest1 >= hcool1,  t1 == 1800 + hrest1), And(l11,  hrest1 >= 0,  t1 == hrest1), And(l21,  hrest1 >= 1800 + hcool1,  t1 == hrest1)), Not(And(l11, l21)))

DisN = And(t == 900, t0 < 1800, t1 < 1800, t0 >= 0, t1 >= 0)

EqsS = And(Or(And(hheat == hrest0, hheat <= hrest1), And(hheat == hrest1, hheat <= hrest0)), Or(And(hcool == hcool0, hcool <= hcool1), And(hcool == hcool1, hcool <= hcool0)))
Gih = And(Invrod0, Invcontroller, Invrod1, EqsS)
dead = And(Gih, DisN)
EqsC = And(Or(And(hcool == hcoolcool0, hcoolcool0 <= hcoolcool1), And(hcool == hcoolcool1, hcoolcool1 <= hcoolcool0)), hcool1 == hcoolcool1, Or(And(hheat == hheatrest0, hheatrest0 <= hheatrest1), And(hheat == hheatrest1, hheatrest1 <= hheatrest0)), hcool0 == hcoolcool0, hrest0 == hheatrest0, hrest1 == hheatrest1)
#Sep = And(Or(hcoolcool0 - hcoolcool1 >= 900, hcoolcool1 - hcoolcool0 >= 900), Or(hheatrest0 - hheatrest1 >= 1350, hheatrest1 - hheatrest0 >= 1350))
Sep = And(hcoolcool0 - hcoolcool1 >= 900, hheatrest0 - hheatrest1 >= 1350)
GihExt = And(Invrod0, Invcontroller, Invrod1, EqsS, EqsC, Sep)
deadExt = And(GihExt, DisN)
print "Solving deadExt:" 
getCEX(deadExt)
