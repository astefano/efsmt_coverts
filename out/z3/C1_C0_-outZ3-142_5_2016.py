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
r, y = Ints('r y')
q, x = Ints('q x')



ciC1 = And(Or(And(c10,  3 >= y,  y >= 0), And(c11,  3 >= y,  y >= 0,  3 >= r), And(c10,  3 >= y,  y >= 0,  3 >= r)), Not(And(c10, c11)))

ciC0 = And(Or(And(c00,  7 >= x,  x >= 0), And(c01,  10 >= x,  x >= 0,  x >= q,  7 >= q), And(c00,  7 >= x,  x >= 0,  7 >= q)), Not(And(c00, c01)))


#abstract reach
absReachII = Or(And(c11, c01), And(c10, c00), And(c10, c01), And(c10, c00), And(c11, c00)) 

#Enabled guided by absReach
En = Or(And(c11, c01, -y >= -3, -x >= -10), And(c10,c00, -q + x >= 0, -y >= -3, -x >= -7), And(c10,c01, -r + y >= 0, -y >= -3, -x >= -10), And(c10,c00, -r + y >= 0, -y >= -3, -x >= -7), And(c11,c00, -q + x >= 0, -y >= -3, -x >= -7))

DisN = Not(En)

NewCond = True

PosClks = And(r >= 0, q >= 0)
Gi = And(ciC0, ciC1, absReachII)

bad = And(Gi, x < y)
print "Solving bad:" 
getCEX(bad)

safe = Implies(c01, x >= y)
#Solving EF formula: 
EFformula = Exists([r,q], And(r <= 3, q <= 7, PosClks, ForAll([c10, c11, c00, c01, y, x], Implies(And(x >= 0, y >= 0, Gi), And(safe, En)))))
#EFformula = Exists([r,q], ForAll([c20, c21, c10, c11, y, x],  And(PosClks, Implies(Gi, And(safe)))))
#EFformula = Exists([r,q], And(PosClks, Implies(Gi, And(safe))))
#EFformula = Exists([q], ForAll(x, Implies(x >= q, x >= 4)))
#EFformula = Exists([q], Implies(x >= q, x >= 4))
s = Solver() 
s.add(EFformula) 
print s.check() 
print s.model()
