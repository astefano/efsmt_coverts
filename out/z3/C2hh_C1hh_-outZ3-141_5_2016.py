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



c20, c21 = Bools('c20 c21')
c10, c11 = Bools('c10 c11')
hc, ha2, y, r = Ints('hc ha2 y r')
ha1, hb, x, q = Ints('ha1 hb x q')



ciC2hh = And(Or(And(c20,  5 >= y,  y >= 0,  y == hc,  y == ha2), And(c21,  3 >= y,  y >= 0,  y + 5 >= ha2,  ha2 >= y,  ha2 >= r + y,  y == hc), And(c20,  5 >= y,  hc >= y,  y >= 0,  y + 3 >= hc,  5 >= r,  y == ha2)), Not(And(c20, c21)))

ciC1hh = And(Or(And(c10,  7 >= x,  x >= 0,  x == hb,  x == ha1), And(c11,  10 >= x,  x >= hb,  hb >= 0,  hb + 7 >= x,  x >= q + hb,  x == ha1), And(c10,  7 >= x,  hb >= x,  x >= 0,  x + 10 >= hb,  7 >= q,  x + 10 >= q + hb,  x == ha1)), Not(And(c10, c11)))


#abstract reach
absReachII = Or(And(c20, c10), And(c20, c11), And(c21, c10), And(c21, c11), And(c20, c10)) 

#Enabled guided by absReach
En = Or(And(c20,c10, -r + y >= 0, -y >= -5, -x >= -7), And(c20,c11, -r + y >= 0, -y >= -5, -x >= -10), And(c21,c10, -q + x >= 0, -y >= -3, -x >= -7), And(c21, c11, -y >= -3, -x >= -10), And(c20,c10, -q + x >= 0, -y >= -5, -x >= -7))

DisN = Not(En)

NewCond = True

ha1a2, hb, hc = Ints('ha1a2 hb hc')
EqsS = ha1 == ha2
Gih = And(ciC2hh, ciC1hh, EqsS, absReachII, NewCond)
dead = And(Gih, DisN)
EqsC = And(ha1 == ha1a2, ha2 == ha1a2, hb == hb, hc == hc)
Sep = True
GihExt = And(ciC2hh, ciC1hh, EqsS, EqsC, Sep, absReachII, NewCond)
deadExt = And(GihExt, DisN)
print "Solving deadExt:" 
getCEX(deadExt)



PosClks = And(hc >= 0, ha2 >= 0, y >= 0, r >= 0, ha1 >= 0, hb >= 0, x >= 0, q >= 0, ha1a2 >= 0, hb >= 0, hc >= 0)
Gi = And(ciC2hh, ciC1hh, absReachII, NewCond, PosClks)
safe = True
#Solving EF formula: 
EFformula = Exists([hc, ha2, ha1, hb, ha1a2, hb, hc], ForAll([c20, c21, c10, c11, y, r, x, q], Implies(Gih, And(safe, En))))
s = Solver() 
s.add(EFformula) 
print s.check() 
print s.model()