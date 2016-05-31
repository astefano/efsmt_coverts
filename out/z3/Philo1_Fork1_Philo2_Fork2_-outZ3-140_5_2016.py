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
beta1, ts1, eta1, gamma1, t1, alpha1 = Ints('beta1 ts1 eta1 gamma1 t1 alpha1')

eta2, alpha2, beta2, ts2, t2, gamma2 = Ints('eta2 alpha2 beta2 ts2 t2 gamma2')






ciPhilo1 = And(Or(And(p11,  gamma1 >= ts1,  ts1 >= 0,  ts1 == t1), And(p12,  3 >= t1,  gamma1 + t1 >= ts1,  ts1 >= t1,  t1 >= 0,  ts1 >= eta1 + t1), And(p13,  3 >= t1,  gamma1 >= 0,  gamma1 + t1 + 3 >= ts1,  gamma1 >= eta1,  ts1 >= 2 + t1,  t1 >= 0,  ts1 >= 2 + eta1 + t1), And(p10,  alpha1 >= t1,  gamma1 >= 0,  gamma1 + t1 + 3 >= ts1,  gamma1 >= eta1,  ts1 >= 2 + t1,  t1 >= 2,  ts1 >= 2 + eta1 + t1), And(p11,  alpha1 >= 2,  alpha1 + gamma1 + 3 >= beta1,  gamma1 >= ts1,  gamma1 >= eta1,  ts1 >= 0,  ts1 == t1), And(p12,  3 >= t1,  alpha1 >= 2,  alpha1 + gamma1 + 3 >= beta1,  gamma1 + t1 >= ts1,  ts1 >= t1,  t1 >= 0,  ts1 >= eta1 + t1), And(p13,  3 >= t1,  alpha1 >= 2,  alpha1 + gamma1 + 3 >= beta1,  gamma1 >= 0,  gamma1 + t1 + 3 >= ts1,  gamma1 >= eta1,  ts1 >= 2 + t1,  t1 >= 0,  ts1 >= 2 + eta1 + t1), And(p10,  alpha1 >= t1,  alpha1 + gamma1 + 3 >= beta1,  gamma1 >= 0,  gamma1 + t1 + 3 >= ts1,  gamma1 >= eta1,  ts1 >= 2 + t1,  t1 >= 2,  ts1 >= 2 + eta1 + t1)), Not(Or(And(p11, p12), And(p11, p13), And(p11, p10), And(p12, p13), And(p12, p10), And(p13, p10))))

ciFork1 = And(Or(f10, f11), Not(And(f10, f11)))

ciPhilo2 = And(Or(And(p21,  gamma2 >= ts2,  ts2 >= 0,  ts2 == t2), And(p22,  4 >= t2,  gamma2 + t2 >= ts2,  ts2 >= t2,  t2 >= 0,  ts2 >= eta2 + t2), And(p23,  2 >= t2,  gamma2 >= 0,  gamma2 + t2 + 4 >= ts2,  gamma2 >= eta2,  ts2 >= 3 + t2,  t2 >= 0,  ts2 >= 3 + eta2 + t2), And(p20,  alpha2 >= t2,  gamma2 >= 0,  gamma2 + t2 + 4 >= ts2,  gamma2 >= eta2,  ts2 >= 3 + t2,  t2 >= 1,  ts2 >= 3 + eta2 + t2), And(p21,  alpha2 >= 1,  alpha2 + gamma2 + 4 >= beta2,  gamma2 >= ts2,  gamma2 >= eta2,  ts2 >= 0,  ts2 == t2), And(p22,  4 >= t2,  alpha2 >= 1,  alpha2 + gamma2 + 4 >= beta2,  gamma2 + t2 >= ts2,  ts2 >= t2,  t2 >= 0,  ts2 >= eta2 + t2), And(p23,  2 >= t2,  alpha2 >= 1,  alpha2 + gamma2 + 4 >= beta2,  gamma2 >= 0,  gamma2 + t2 + 4 >= ts2,  gamma2 >= eta2,  ts2 >= 3 + t2,  t2 >= 0,  ts2 >= 3 + eta2 + t2), And(p20,  alpha2 >= t2,  alpha2 + gamma2 + 4 >= beta2,  gamma2 >= 0,  gamma2 + t2 + 4 >= ts2,  gamma2 >= eta2,  ts2 >= 3 + t2,  t2 >= 1,  ts2 >= 3 + eta2 + t2)), Not(Or(And(p21, p22), And(p21, p23), And(p21, p20), And(p22, p23), And(p22, p20), And(p23, p20))))

ciFork2 = And(Or(f20, f21), Not(And(f20, f21)))


#abstract reach
absReachII = Or(And(p11, f10, p21, f20), And(p11, f10, p20, f20), And(p11, f11, p23, f21), And(p11, f10, p22, f21), And(p10, f10, p21, f20), And(p12, f11, p21, f20), And(p11, f10, p22, f21), And(p12, f11, p21, f20), And(p12, f11, p20, f20), And(p11, f10, p21, f20), And(p10, f10, p20, f20), And(p10, f11, p23, f21), And(p13, f11, p20, f21), And(p13, f11, p21, f21), And(p10, f10, p22, f21)) 

#Enabled guided by absReach
En = Or(And(p11, f10, p21, f20, -eta1 + t1 >= 0, -t1 + gamma1 >= 0, -t2 + gamma2 >= 0), And(p11, f10, p20, f20, -eta1 + t1 >= 0, -t1 + gamma1 >= 0, -t2 + alpha2 >= 0), And(p11, f11, p23, f21, -t2 + alpha2 >= 0, -t1 + gamma1 >= 0, -t2 >= -2), And(p11, f10, p22, f21, -t1 + gamma1 >= 0, -t2 >= -4), And(p10, f10, p21, f20, t2 - eta2 >= 0, -t2 + gamma2 >= 0, alpha1 - t1 >= 0), And(p12, f11, p21, f20, -t2 + gamma2 >= 0, -t1 >= -3), And(p11, f10, p22, f21, -eta1 + t1 >= 0, -t1 + gamma1 >= 0, -t2 >= -4), And(p12, f11, p21, f20, t2 - eta2 >= 0, -t2 + gamma2 >= 0, -t1 >= -3), And(p12, f11, p20, f20, -t2 + alpha2 >= 0, -t1 >= -3), And(p11, f10, p21, f20, t2 - eta2 >= 0, -t1 + gamma1 >= 0, -t2 + gamma2 >= 0), And(p10, f10, p20, f20, -beta1 + ts1 >= 0, ts2 - beta2 >= 0, -t2 + alpha2 >= 0, alpha1 - t1 >= 0), And(p10, f11, p23, f21, alpha1 - t1 >= 0, -t2 + alpha2 >= 0, -t2 >= -2), And(p13, f11, p20, f21, alpha1 - t1 >= 0, -t2 + alpha2 >= 0, -t1 >= -3), And(p13, f11, p21, f21, alpha1 - t1 >= 0, -t2 + gamma2 >= 0, -t1 >= -3), And(p10, f10, p22, f21, alpha1 - t1 >= 0, -t2 >= -4))

DisN = Not(En)

NewCond = True

Kparams = And(gamma1 >= eta1, alpha1 + gamma1 + 3 >= beta1, alpha1 >= 2, gamma2 >= eta2, alpha2 + gamma2 + 4 >= beta2, alpha2 >= 1)

PosParams = And(beta1 >= 3, eta1 >= 0, gamma1 >= 1, alpha1 >= 4, eta2 >= 1, alpha2 >= 3, beta2 >= 4, gamma2 >= 4)

PosClks = And(ts2 >= 0, t2 >= 0, ts1 >= 0, t1 >= 0)

Gi = And(ciPhilo1, ciFork1, ciPhilo2, ciFork2, absReachII, NewCond, PosClks)
safe = t1 <= ts2
#Solving EF formula: 
EFformula = Exists([beta1, eta1, gamma1, alpha1, eta2, alpha2, beta2, gamma2], ForAll([p11, p12, p13, p10, f10, f11, p21, p22, p23, p20, f20, f21, ts1, t1, ts2, t2], And(PosParams, Kparams, Implies(Gi, And(safe, En)))))
s = Solver() 
s.add(EFformula) 
print s.check() 
print s.model()
