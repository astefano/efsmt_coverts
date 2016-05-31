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



far, near, in0 = Bools('far near in')
C0, C1, C2, C3 = Bools('C0 C1 C2 C3')
is_up, coming_down, is_down, going_up = Bools('is_up coming_down is_down going_up')
x, het0, hat0, t0, t2, t1, heps = Ints('x het0 hat0 t0 t2 t1 heps')
hac, hrc, c2, hlc, c1, hec, c0, z = Ints('hac hrc c2 hlc c1 hec c0 z')
y, g2, g1, hepsg, g0, hlg, hrg = Ints('y g2 g1 hepsg g0 hlg hrg')

ciTrainhh = And(Or(And(far,  heps >= 0,  x == heps,  het0 == heps,  hat0 == heps), And(near,  t0 >= x,  het0 >= x,  x >= 0,  x == hat0,  het0 == heps), And(in0,  t0 + heps >= x,  t2 >= x,  x >= heps,  heps >= 0,  het0 >= x,  x >= t1 + heps,  x == hat0), And(far,  t0 + heps >= x,  t2 + het0 >= x,  x >= heps,  het0 >= 0,  heps >= het0,  x >= t1 + heps,  x == hat0), And(near,  t0 >= x,  t0 >= t1,  t2 + het0 >= heps,  het0 >= x,  x >= 0,  heps >= het0,  t2 + het0 >= t1 + heps,  x == hat0)))#, 

not2LocTrain = Not(Or(And(far, near), And(far, in0), And(near, in0)))

cicontrollerhh = And(Or(And(C0,  z >= 0,  hac == z,  hrc == z,  hlc == z,  hec == z), And(C1,  c0 >= hac,  hrc >= hac,  hac >= 0,  hrc == hlc,  hrc == hec,  hac == z), And(C2,  c0 >= c1,  c1 >= 0,  hrc >= z,  z >= c1,  c1 + hlc == z,  hac == z,  hrc == hec), And(C3,  c0 >= c1,  c1 >= 0,  c2 >= hec,  hec >= 0,  hrc >= hac,  hac >= c1 + hec,  c1 + hlc == hac,  hec == z), And(C0,  c0 >= c1,  c1 >= 0,  c2 + hrc >= hec,  hrc >= 0,  hec >= hrc,  hac >= c1 + hec,  c1 + hlc == hac,  hec == z), And(C1,  c0 >= hac,  c0 >= c1,  c1 >= 0,  c2 + hrc >= hec,  hrc >= hac,  hlc >= hec,  hac >= 0,  hec >= hrc,  hac == z), And(C2,  c0 >= c1,  c1 >= 0,  c2 + hrc >= hec,  hrc >= z,  hec >= hrc,  z >= c1,  c1 + hlc == z,  hac == z)), Not(Or(And(C0, C1), And(C0, C2), And(C0, C3), And(C1, C2), And(C1, C3), And(C2, C3))))

cigatehh = And(Or(And(is_up,  hrg >= 0,  y == hrg,  hepsg == hrg,  hlg == hrg), And(coming_down,  g0 >= y,  hepsg >= y,  y >= 0,  y == hlg,  hepsg == hrg), And(is_down,  g0 + hepsg >= y,  y >= hepsg,  hepsg >= 0,  hrg >= y,  y == hlg), And(going_up,  g0 + hepsg >= hlg,  g1 >= y,  hepsg >= y,  y >= 0,  hlg >= hepsg,  y == hrg), And(is_up,  g0 >= 0,  g1 + hepsg >= y,  y >= hepsg,  hepsg >= 0,  hlg >= y,  y >= g2 + hepsg,  y == hrg), And(coming_down,  g0 >= y,  g1 + hepsg >= hrg,  hepsg >= y,  y >= 0,  hrg >= hepsg,  hrg >= g2 + hepsg,  y == hlg), And(is_down,  g0 + hepsg >= y,  g1 >= 0,  g1 >= g2,  y >= hepsg,  hepsg >= 0,  hrg >= y,  hrg >= g2 + y,  y == hlg), And(going_up,  g0 + hepsg >= hlg,  g1 >= y,  g1 >= g2,  hepsg >= y,  y >= 0,  hlg >= hepsg,  y == hrg)), Not(Or(And(is_up, coming_down), And(is_up, is_down), And(is_up, going_up), And(coming_down, is_down), And(coming_down, going_up), And(is_down, going_up))))


#abstract reach
absReachII = Or(And(in0, C2, coming_down), And(near, C1, is_up), And(in0, C1, is_up), And(near, C2, coming_down), And(near, C1, is_up), And(far, C0, is_up)) 

#Enabled guided by absReach
En = Or(And(in0, C2, coming_down, -x + t2 >= 0, g0 - y >= 0), And(near,C1,is_up, x - t1 >= 0, -x + t0 >= 0, -x + t2 >= 0, c0 - z >= 0), And(in0, C1, is_up, c1 - z == 0, -x + t2 >= 0, -c1 + c0 >= 0), And(near,C2,coming_down, x - t1 >= 0, -x + t0 >= 0, -x + t2 >= 0, g0 - y >= 0), And(near, C1, is_up, c1 - z == 0, -x + t0 >= 0, -c1 + c0 >= 0), And(far, C0, is_up))

DisN = Not(En)

NewCond = True

hrcrg, hlclg, hecet0, hacat0 = Ints('hrcrg hlclg hecet0 hacat0')
EqsS = And(hac == hat0, hec == het0, hlc == hlg, hrc == hrg)
Gih = And(ciTrainhh, cicontrollerhh, cigatehh, EqsS, absReachII, NewCond)
dead = And(Gih, DisN)
EqsC = And(hac == hacat0, hlg == hlclg, hrg == hrcrg, het0 == hecet0, hrc == hrcrg, hat0 == hacat0, hec == hecet0, hlc == hlclg)
Sep = Implies(in0, is_down)
GihExt = And(ciTrainhh, cicontrollerhh, cigatehh, EqsS, EqsC, Sep, absReachII, NewCond)
deadExt = And(GihExt, DisN)
print "Solving deadExt:" 
getCEX(deadExt)

Kparams = And(t2 >= t1, t0 >= t1, c0 >= c1, g1 >= g2)

Params = And(c2 >= 0, c1 >= 0, c0 >= 0, g2 >= 0, g1 >= 0, g0 >= 0, t0 >= 0, t2 >= 0, t1 >= 0)

PosClks = And(x >= 0, het0 >= 0, hat0 >= 0, heps >= 0, hac >= 0, hrc >= 0, hlc >= 0, hec >= 0, z >= 0, y >= 0, hepsg >= 0, hlg >= 0, hrg >= 0, hrcrg >= 0, hlclg >= 0, hecet0 >= 0, hacat0 >= 0, heps >= 0)
Gi = And(ciTrainhh, cicontrollerhh, cigatehh, absReachII, NewCond, PosClks)
safe = True
#Solving EF formula: 
EFformula = Exists([t0, t2, t1, c2, c1, c0, g2, g1, g0], ForAll([far, near, in0, C0, C1, C2, C3, is_up, coming_down, is_down, going_up, x, z, y, het0, hat0, hac, hrc, hlc, hec, hepsg, hlg, hrg, hrcrg, hlclg, hecet0, hacat0, heps], Implies(Gih, And(safe, En))))
s = Solver() 
s.add(EFformula) 
print s.check() 
print s.model()

print Tactic('qe2').apply(Exists([het0, hat0, hac, hrc, hlc, hec, hepsg, hlg, hrg, hrcrg, hlclg, hecet0, hacat0, heps], Gih))

res = Tactic('qe2').apply(Exists([het0, hat0, heps, x], ciTrainhh)).as_expr()
print res

#print substitute(And(t2 >= t1), (t2, IntVal('1')), (t1, IntVal('2')))
