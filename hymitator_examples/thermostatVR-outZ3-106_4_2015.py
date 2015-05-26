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


hturn_onturn_onH, hturn_offturn_offH = Ints('hturn_onturn_onH hturn_offturn_offH')


x = Int('x')

M = Int('M')

K = Int('K')

l0 = Bool('l0')

hturn_off = Int('hturn_off')

l1 = Bool('l1')

m = Int('m')

hturn_on = Int('hturn_on')

h = Int('h')



Invthermostat = And(Or(And(l0,  x>= 16, hturn_on > hturn_off,  hturn_off >= 0,  m == 16,  M == 20,  K == 2,  h == 1), And(l1, x<= 20,	 hturn_on >= 0,  hturn_off >= hturn_on,  m == 16,  M == 20,  K == 2,  h == 1), And(l0, x>= 16, hturn_on >= hturn_off,  hturn_off >= 0,  m == 16,  M == 20,  K == 2,  h == 1)), Not(And(l0, l1)))


on = Bool('on')

x = Int('x')

hturn_offH = Int('hturn_offH')

M = Int('M')

K = Int('K')

m = Int('m')

off = Bool('off')

hturn_onH = Int('hturn_onH')

h = Int('h')



Invheater = And(Or(And(off,  hturn_offH >= 0,  m == 16,  M == 20,  K == 2,  h == 1,  x + 2*hturn_offH == 20), And(on,  hturn_offH >= hturn_onH,  m == 16,  M == 20,  K == 2,  h == 1,  x + 2*hturn_offH == 20 + 5*hturn_onH), And(off,  hturn_onH >= 0,  3*hturn_offH + 20 >= x + 5*hturn_onH,  m == 16,  M == 20,  K == 2,  h == 1), And(on,  hturn_onH >= 0,  3*hturn_offH + 20 >= x		,  m == 16,  M == 20,  K == 2,  h == 1)), Not(And(on, off)))

DisN = Or(x < m, x > M)

II = Or(And(l0, off), And(l1, on))

EqsS = And(hturn_off == hturn_offH, hturn_on == hturn_onH)
Gih = And(Invthermostat, Invheater, EqsS)
dead = And(Gih, DisN)
EqsC = And(hturn_on == hturn_onturn_onH, hturn_onH == hturn_onturn_onH, hturn_off == hturn_offturn_offH, hturn_offH == hturn_offturn_offH)
Sep = True
GihExt = And(Invthermostat, Invheater, EqsS, EqsC, Sep, II)
deadExt = And(GihExt, DisN)
print "Solving deadExt:" 
getCEX(deadExt)
