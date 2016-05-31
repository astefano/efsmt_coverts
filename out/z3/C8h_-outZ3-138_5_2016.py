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



c0, c1, c2 = Bools('c0 c1 c2')
p, ha, q, x, y = Ints('p ha q x y')


ciC8 = And(Or(And(c0,  p >= x,  x >= 0,  x == y), And(c1,  p >= 0,  x >= p,  10 >= x,  x == y), And(c2,  p >= 0,  q >= x,  y >= 0,  y + 10 >= x,  x >= p + y), And(c0,  p >= x,  y >= x,  x >= 0,  q + x >= p + y,  10 >= p), And(c1,  p >= 0,  q + x >= p + y,  x >= p,  10 >= y,  y >= x)), Not(Or(And(c0, c1), And(c0, c2), And(c1, c2))))

ciC8h = And(Or(And(c0,  p >= x,  x >= 0,  x == y,  x == ha), And(c1,  p >= 0,  x >= p,  10 >= x,  x == y,  p + ha == x), And(c2,  p >= 0,  q >= x,  y >= 0,  y + 10 >= x,  x >= p + y,  y == ha), And(c0,  p >= x,  y >= x,  x >= 0,  q + x >= p + y,  10 >= p,  x == ha), And(c1,  p >= 0,  q + x >= p + y,  x >= p,  10 >= y,  y >= x,  p + ha == x)), Not(Or(And(c0, c1), And(c0, c2), And(c1, c2))))

#And(c0, x <= p, p -x <= 10 - y), And(c1, y <= 10, q >= 0, q >= 10 + x -y), And(c2, 0 <= p, x - y <= p))
#abstract reach
absReachII = Or(c0, c1, c2) 

En = Or(And(c0, x <= p, p -x <= 10 - y), And(c1, y <= 10, q >= 0, q >= 10 + x -y), And(c2, 0 <= p, x - y <= p))

Fh = Implies(And(absReachII, ciC8h), x <= 10)

fh= Exists([p, q, ha], ForAll([x,y, c0, c1, c2], Fh))


I = And(absReachII, ciC8, And(x>=0, y >=0))

safe = And(x <= 10, absReachII)

F = Implies(I, En)

f = Exists([p, q], ForAll([x,y, c0, c1, c2], F))

s = Solver()
s.add(f)

res = s.check()
print res
#print "*" + res + "*"
#if res == "sat" : 
print s.model()

F0 = substitute(F, (p, IntVal(10)), (q, IntVal(10)))

print simplify(F0)

s0 = Solver()
s0.add(F0)
print s0.check()

