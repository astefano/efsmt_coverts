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

lc2 = Bool('lc2')

l10 = Bool('l10')

lc3 = Bool('lc3')

lc1 = Bool('lc1')

l11 = Bool('l11')

t0 = Int('t0')

M = Int('M')

vr1 = Int('vr1')

t1 = Int('t1')

m = Int('m')

T = Int('T')

t = Int('t')

vr0 = Int('vr0')

l21 = Bool('l21')

l20 = Bool('l20')



InvtccAll = Or(And(lc1, l10, l11,  t >= 0,  m == 3,  M == 15,  T == 6,  t + 36 == 6*t0,  t + 36 == 6*t1), And(lc2, l20, l11,  15 >= t,  m == 3,  M == 15,  T == 6,  t + 2*t0 == 32,  t + 2*t1 == 32), And(lc3, l10, l21,  15 >= t,  m == 3,  M == 15,  T == 6,  t + 2*t0 == 32,  t + 2*t1 == 32), And(lc1, l10, l11,  t >= 3,  m == 3,  M == 15,  T == 6,  t == 3 + 6*t0,  t + 84 == 6*t1), And(lc1, l10, l11,  t >= 3,  m == 3,  M == 15,  T == 6,  t + 84 == 6*t0,  t == 3 + 6*t1), And(lc3, l10, l21,  15 >= t,  m == 3,  M == 15,  T == 6,  t + 2*t0 == 19,  t + 2*t1 == 48), And(lc2, l20, l11,  15 >= t,  m == 3,  M == 15,  T == 6,  t + 2*t0 == 48,  t + 2*t1 == 19), And(lc1, l10, l11,  t >= 3,  m == 3,  M == 15,  T == 6,  t + 45 == 6*t0,  t == 3 + 6*t1), And(lc1, l10, l11,  t >= 3,  m == 3,  M == 15,  T == 6,  t == 3 + 6*t0,  t + 45 == 6*t1), And(lc2, l20, l11,  15 >= t,  m == 3,  M == 15,  T == 6,  t + 2*t0 == 35,  t + 2*t1 == 19), And(lc3, l10, l21,  15 >= t,  m == 3,  M == 15,  T == 6,  t + 2*t0 == 19,  t + 2*t1 == 35))

not2Locs = Not(Or(And(lc1, lc2), And(lc1, lc3), And(lc2, lc3), And(l10, l20), And(l11, l21)))

DisN = And(not2Locs, t == m, t0 < T, t1 < T, t0 >= 0, t1 >= 0)

Gih = And(InvtccAll)
dead = And(Gih, DisN)
print "Solving dead:" 
getCEX(dead)
