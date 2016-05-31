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



c10, c11 = Bools('c10 c11')
c00, c01 = Bools('c00 c01')
hc1, hb, r, y = Ints('hc1 hb r y')
q, x, hc0, ha = Ints('q x hc0 ha')



ciC1hh = And(Or(And(c10,  3 >= y,  y >= 0,  y == hb,  y == hc1), And(c11,  3 >= y,  y >= 0,  y + 3 >= hc1,  hc1 >= y,  hc1 >= r + y,  y == hb), And(c10,  3 >= y,  hb >= y,  y >= 0,  y + 3 >= hb,  3 >= r,  y == hc1)), Not(And(c10, c11)))

ciC0hh = And(Or(And(c00,  7 >= x,  x >= 0,  x == ha,  x == hc0), And(c01,  10 >= x,  x >= ha,  ha >= 0,  ha + 7 >= x,  x >= q + ha,  x == hc0), And(c00,  7 >= x,  ha >= x,  x >= 0,  x + 10 >= ha,  7 >= q,  x + 10 >= q + ha,  x == hc0)), Not(And(c00, c01)))


#abstract reach
absReachII = Or(And(c11, c01), And(c10, c00), And(c10, c01), And(c10, c00), And(c11, c00)) 

#Enabled guided by absReach
En = Or(And(c11, c01, -y >= -3, -x >= -10), And(c10,c00, -q + x >= 0, -y >= -3, -x >= -7), And(c10,c01, -r + y >= 0, -y >= -3, -x >= -10), And(c10,c00, -r + y >= 0, -y >= -3, -x >= -7), And(c11,c00, -q + x >= 0, -y >= -3, -x >= -7))

DisN = Not(En)

NewCond = True

hc0c1 = Int('hc0c1')
EqsS = hc0 == hc1
Gih = And(ciC1hh, ciC0hh, EqsS, absReachII, NewCond)
dead = And(Gih, DisN)
EqsC = And(hc0 == hc0c1, hc1 == hc0c1)
Sep = True
GihExt = And(ciC1hh, ciC0hh, EqsS, EqsC, Sep, absReachII, NewCond)
deadExt = And(GihExt, DisN)
print "Solving deadExt:" 
getCEX(deadExt)

Kparams = And(r <= 3, q <= 7)
Params = And(r >= 0, q >= 0)
PosClks = And(hc1 >= 0, hb >= 0, y >= 0, x >= 0, hc0 >= 0, ha >= 0, hc0c1 >= 0)
Gi = And(ciC1hh, ciC0hh, absReachII, NewCond, PosClks)
safe = x < y
#Solving EF formula: 
EFformula = Exists([r, q], ForAll([c10, c11, c00, c01, y, x, hc1, hb, hc0, hc0c1, ha], And(Params, Kparams, Implies(Gih, And(safe, En)))))
s = Solver() 
s.add(EFformula) 
print s.check() 
print s.model()