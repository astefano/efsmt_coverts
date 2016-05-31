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



far_1, near_1, in_1 = Bools('far_1 near_1 in_1')
far_0, near_0, in_0 = Bools('far_0 near_0 in_0')
C0, C1, C2, C3 = Bools('C0 C1 C2 C3')
is_up, coming_down, is_down, going_up = Bools('is_up coming_down is_down going_up')
t1_1, het_1, hat_1, t2_1, hepst_1, x_1, t0_1 = Ints('t1_1 het_1 hat_1 t2_1 hepst_1 x_1 t0_1')
hepst_0, hat_0, t1_0, t2_0, het_0, x_0, t0_0 = Ints('hepst_0 hat_0 t1_0 t2_0 het_0 x_0 t0_0')
hac, hrc, c2, hlc, c1, hec, c0, z = Ints('hac hrc c2 hlc c1 hec c0 z')
y, g2, g1, hepsg, g0, hlg, hrg = Ints('y g2 g1 hepsg g0 hlg hrg')





citrain_1hh = Or(And(far_1,  x_1 >= 0,  het_1 == x_1,  hat_1 == x_1,  hepst_1 == x_1), And(near_1,  t0_1 >= hat_1,  het_1 >= hat_1,  hat_1 >= 0,  het_1 == hepst_1,  hat_1 == x_1), And(in_1,  t0_1 + hepst_1 >= hat_1,  t2_1 >= hat_1,  het_1 >= hat_1,  hat_1 >= hepst_1,  hepst_1 >= 0,  hat_1 >= t1_1 + hepst_1,  hat_1 == x_1), And(far_1,  t0_1 + hepst_1 >= hat_1,  t2_1 + het_1 >= hat_1,  het_1 >= 0,  hat_1 >= hepst_1,  hepst_1 >= het_1,  hat_1 >= t1_1 + hepst_1,  hat_1 == x_1), And(near_1,  t0_1 >= hat_1,  t0_1 >= t1_1,  t2_1 + het_1 >= hepst_1,  het_1 >= hat_1,  hat_1 >= 0,  hepst_1 >= het_1,  t2_1 + het_1 >= t1_1 + hepst_1,  hat_1 == x_1))

NotAt2Locs_train_1hh  = Not(Or(And(far_1, near_1), And(far_1, in_1), And(near_1, in_1)))

Kp_train_1hh = And(Tactic('qe2').apply(Exists([het_1,hat_1,hepst_1,x_1], And( x_1 >= 0, het_1 == x_1, hat_1 == x_1, hepst_1 == x_1))).as_expr(), Tactic('qe2').apply(Exists([het_1,hat_1,hepst_1,x_1], And( t0_1 >= hat_1, het_1 >= hat_1, hat_1 >= 0, het_1 == hepst_1, hat_1 == x_1))).as_expr(), Tactic('qe2').apply(Exists([het_1,hat_1,hepst_1,x_1], And( t0_1 + hepst_1 >= hat_1, t2_1 >= hat_1, het_1 >= hat_1, hat_1 >= hepst_1, hepst_1 >= 0, hat_1 >= t1_1 + hepst_1, hat_1 == x_1))).as_expr(), Tactic('qe2').apply(Exists([het_1,hat_1,hepst_1,x_1], And( t0_1 + hepst_1 >= hat_1, t2_1 + het_1 >= hat_1, het_1 >= 0, hat_1 >= hepst_1, hepst_1 >= het_1, hat_1 >= t1_1 + hepst_1, hat_1 == x_1))).as_expr())

citrain_0hh = Or(And(far_0,  x_0 >= 0,  hepst_0 == x_0,  hat_0 == x_0,  het_0 == x_0), And(near_0,  t0_0 >= hat_0,  hepst_0 >= hat_0,  hat_0 >= 0,  hepst_0 == het_0,  hat_0 == x_0), And(in_0,  t0_0 + hepst_0 >= hat_0,  t2_0 >= hat_0,  hepst_0 >= 0,  het_0 >= hat_0,  hat_0 >= hepst_0,  hat_0 >= t1_0 + hepst_0,  hat_0 == x_0), And(far_0,  t0_0 + hepst_0 >= hat_0,  t2_0 + het_0 >= hat_0,  hepst_0 >= het_0,  het_0 >= 0,  hat_0 >= hepst_0,  hat_0 >= t1_0 + hepst_0,  hat_0 == x_0), And(near_0,  t0_0 >= hat_0,  t0_0 >= t1_0,  t2_0 + het_0 >= hepst_0,  hepst_0 >= het_0,  het_0 >= hat_0,  hat_0 >= 0,  t2_0 + het_0 >= t1_0 + hepst_0,  hat_0 == x_0))

NotAt2Locs_train_0hh  = Not(Or(And(far_0, near_0), And(far_0, in_0), And(near_0, in_0)))

Kp_train_0hh = And(Tactic('qe2').apply(Exists([hepst_0,hat_0,het_0,x_0], And( x_0 >= 0, hepst_0 == x_0, hat_0 == x_0, het_0 == x_0))).as_expr(), Tactic('qe2').apply(Exists([hepst_0,hat_0,het_0,x_0], And( t0_0 >= hat_0, hepst_0 >= hat_0, hat_0 >= 0, hepst_0 == het_0, hat_0 == x_0))).as_expr(), Tactic('qe2').apply(Exists([hepst_0,hat_0,het_0,x_0], And( t0_0 + hepst_0 >= hat_0, t2_0 >= hat_0, hepst_0 >= 0, het_0 >= hat_0, hat_0 >= hepst_0, hat_0 >= t1_0 + hepst_0, hat_0 == x_0))).as_expr(), Tactic('qe2').apply(Exists([hepst_0,hat_0,het_0,x_0], And( t0_0 + hepst_0 >= hat_0, t2_0 + het_0 >= hat_0, hepst_0 >= het_0, het_0 >= 0, hat_0 >= hepst_0, hat_0 >= t1_0 + hepst_0, hat_0 == x_0))).as_expr())

cicontrollerhh = Or(And(C0,  z >= 0,  hac == z,  hrc == z,  hlc == z,  hec == z), And(C1,  c0 >= hac,  hrc >= hac,  hac >= 0,  hrc == hlc,  hrc == hec,  hac == z), And(C2,  c0 >= c1,  c1 >= 0,  hrc >= z,  z >= c1,  c1 + hlc == z,  hac == z,  hrc == hec), And(C3,  c0 >= c1,  c1 >= 0,  c2 >= hec,  hec >= 0,  hrc >= hac,  hac >= c1 + hec,  c1 + hlc == hac,  hec == z), And(C0,  c0 >= c1,  c1 >= 0,  c2 + hrc >= hec,  hrc >= 0,  hec >= hrc,  hac >= c1 + hec,  c1 + hlc == hac,  hec == z), And(C1,  c0 >= hac,  c0 >= c1,  c1 >= 0,  c2 + hrc >= hec,  hrc >= hac,  hlc >= hec,  hac >= 0,  hec >= hrc,  hac == z), And(C2,  c0 >= c1,  c1 >= 0,  c2 + hrc >= hec,  hrc >= z,  hec >= hrc,  z >= c1,  c1 + hlc == z,  hac == z))

NotAt2Locs_controllerhh  = Not(Or(And(C0, C1), And(C0, C2), And(C0, C3), And(C1, C2), And(C1, C3), And(C2, C3)))

Kp_controllerhh = And(Tactic('qe2').apply(Exists([hac,hrc,hlc,hec,z], And( z >= 0, hac == z, hrc == z, hlc == z, hec == z))).as_expr(), Tactic('qe2').apply(Exists([hac,hrc,hlc,hec,z], And( c0 >= hac, hrc >= hac, hac >= 0, hrc == hlc, hrc == hec, hac == z))).as_expr(), Tactic('qe2').apply(Exists([hac,hrc,hlc,hec,z], And( c0 >= c1, c1 >= 0, hrc >= z, z >= c1, c1 + hlc == z, hac == z, hrc == hec))).as_expr(), Tactic('qe2').apply(Exists([hac,hrc,hlc,hec,z], And( c0 >= c1, c1 >= 0, c2 >= hec, hec >= 0, hrc >= hac, hac >= c1 + hec, c1 + hlc == hac, hec == z))).as_expr(), Tactic('qe2').apply(Exists([hac,hrc,hlc,hec,z], And( c0 >= c1, c1 >= 0, c2 + hrc >= hec, hrc >= 0, hec >= hrc, hac >= c1 + hec, c1 + hlc == hac, hec == z))).as_expr(), Tactic('qe2').apply(Exists([hac,hrc,hlc,hec,z], And( c0 >= hac, c0 >= c1, c1 >= 0, c2 + hrc >= hec, hrc >= hac, hlc >= hec, hac >= 0, hec >= hrc, hac == z))).as_expr())

cigatehh = Or(And(is_up,  hrg >= 0,  y == hrg,  hepsg == hrg,  hlg == hrg), And(coming_down,  g0 >= y,  hepsg >= y,  y >= 0,  y == hlg,  hepsg == hrg), And(is_down,  g0 + hepsg >= y,  y >= hepsg,  hepsg >= 0,  hrg >= y,  y == hlg), And(going_up,  g0 + hepsg >= hlg,  g1 >= y,  hepsg >= y,  y >= 0,  hlg >= hepsg,  y == hrg), And(is_up,  g0 >= 0,  g1 + hepsg >= y,  y >= hepsg,  hepsg >= 0,  hlg >= y,  y >= g2 + hepsg,  y == hrg), And(coming_down,  g0 >= y,  g1 + hepsg >= hrg,  hepsg >= y,  y >= 0,  hrg >= hepsg,  hrg >= g2 + hepsg,  y == hlg), And(is_down,  g0 + hepsg >= y,  g1 >= 0,  g1 >= g2,  y >= hepsg,  hepsg >= 0,  hrg >= y,  hrg >= g2 + y,  y == hlg), And(going_up,  g0 + hepsg >= hlg,  g1 >= y,  g1 >= g2,  hepsg >= y,  y >= 0,  hlg >= hepsg,  y == hrg))

NotAt2Locs_gatehh  = Not(Or(And(is_up, coming_down), And(is_up, is_down), And(is_up, going_up), And(coming_down, is_down), And(coming_down, going_up), And(is_down, going_up)))

Kp_gatehh = And(Tactic('qe2').apply(Exists([y,hepsg,hlg,hrg], And( hrg >= 0, y == hrg, hepsg == hrg, hlg == hrg))).as_expr(), Tactic('qe2').apply(Exists([y,hepsg,hlg,hrg], And( g0 >= y, hepsg >= y, y >= 0, y == hlg, hepsg == hrg))).as_expr(), Tactic('qe2').apply(Exists([y,hepsg,hlg,hrg], And( g0 + hepsg >= y, y >= hepsg, hepsg >= 0, hrg >= y, y == hlg))).as_expr(), Tactic('qe2').apply(Exists([y,hepsg,hlg,hrg], And( g0 + hepsg >= hlg, g1 >= y, hepsg >= y, y >= 0, hlg >= hepsg, y == hrg))).as_expr(), Tactic('qe2').apply(Exists([y,hepsg,hlg,hrg], And( g0 >= 0, g1 + hepsg >= y, y >= hepsg, hepsg >= 0, hlg >= y, y >= g2 + hepsg, y == hrg))).as_expr(), Tactic('qe2').apply(Exists([y,hepsg,hlg,hrg], And( g0 >= y, g1 + hepsg >= hrg, hepsg >= y, y >= 0, hrg >= hepsg, hrg >= g2 + hepsg, y == hlg))).as_expr(), Tactic('qe2').apply(Exists([y,hepsg,hlg,hrg], And( g0 + hepsg >= y, g1 >= 0, g1 >= g2, y >= hepsg, hepsg >= 0, hrg >= y, hrg >= g2 + y, y == hlg))).as_expr())


#abstract reach
absReachII = Or(And(near_1, far_0, C1, is_up), And(far_1, far_0, C3, is_down), And(far_1, in_0, C1, is_up), And(far_1, far_0, C0, going_up), And(far_1, far_0, C0, going_up), And(near_1, far_0, C2, coming_down), And(near_1, far_0, C1, going_up), And(far_1, near_0, C1, is_up), And(far_1, in_0, C2, is_down), And(far_1, near_0, C1, is_up), And(in_1, far_0, C1, going_up), And(far_1, far_0, C0, going_up), And(in_1, far_0, C2, is_down), And(far_1, in_0, C1, going_up), And(far_1, far_0, C3, coming_down), And(far_1, near_0, C2, coming_down), And(near_1, far_0, C1, going_up), And(in_1, far_0, C1, is_up), And(near_1, far_0, C2, is_down), And(far_1, far_0, C0, is_up), And(far_1, near_0, C1, going_up), And(in_1, far_0, C2, coming_down), And(far_1, far_0, C0, is_up), And(far_1, near_0, C1, going_up), And(far_1, near_0, C2, coming_down), And(near_1, far_0, C1, is_up), And(near_1, far_0, C2, coming_down), And(in_1, far_0, C2, coming_down), And(far_1, in_0, C2, coming_down), And(far_1, near_0, C2, is_down), And(far_1, in_0, C2, coming_down)) 

#Enabled guided by absReach
En = Or(And(near_1, far_0, C1, is_up, c1 - z == 0, -x_1 + t0_1 >= 0, -c1 + c0 >= 0), And(far_1, far_0, C3, is_down, -z + c2 >= 0), And(far_1, in_0, C1, is_up, c1 - z == 0, -x_0 + t2_0 >= 0, -c1 + c0 >= 0), And(And(far_1,far_0,C0,going_up, -y + g1 >= 0), And(far_1,far_0,C0,going_up, -g2 + y >= 0, -y + g1 >= 0)), And(far_1, far_0, C0, going_up, -y + g1 >= 0), And(And(near_1,far_0,C2,coming_down, -x_1 + t0_1 >= 0, -y + g0 >= 0), And(near_1,far_0,C2,coming_down, -x_1 + t0_1 >= 0, -g2 + y >= 0, -y + g0 >= 0)), And(near_1,far_0,C1,going_up, -x_1 + t0_1 >= 0, -x_1 + t2_1 >= 0, -y + g1 >= 0, c0 - z >= 0, x_1 - t1_1 >= 0), And(far_1, near_0, C1, is_up, c1 - z == 0, -x_0 + t0_0 >= 0, -c1 + c0 >= 0), And(far_1, in_0, C2, is_down, -x_0 + t2_0 >= 0), And(far_1,near_0,C1,is_up, -x_0 + t2_0 >= 0, -x_0 + t0_0 >= 0, c0 - z >= 0, x_0 - t1_0 >= 0), And(And(in_1,far_0,C1,going_up, -x_1 + t2_1 >= 0, -y + g1 >= 0, c0 - z >= 0), And(in_1,far_0,C1,going_up, -x_1 + t2_1 >= 0, -g2 + y >= 0, -y + g1 >= 0, c0 - z >= 0)), And(far_1, far_0, C0, going_up, -y + g1 >= 0), And(in_1, far_0, C2, is_down, -x_1 + t2_1 >= 0), And(And(far_1,in_0,C1,going_up, -x_0 + t2_0 >= 0, -y + g1 >= 0, c0 - z >= 0), And(far_1,in_0,C1,going_up, -x_0 + t2_0 >= 0, -g2 + y >= 0, -y + g1 >= 0, c0 - z >= 0)), And(And(far_1,far_0,C3,coming_down, -z + c2 >= 0, -y + g0 >= 0), And(far_1,far_0,C3,coming_down, -z + c2 >= 0, -g2 + y >= 0, -y + g0 >= 0)), And(far_1,near_0,C2,coming_down, -x_0 + t2_0 >= 0, -x_0 + t0_0 >= 0, -y + g0 >= 0, x_0 - t1_0 >= 0), And(And(near_1,far_0,C1,going_up, -x_1 + t0_1 >= 0, -y + g1 >= 0, c0 - z >= 0), And(near_1,far_0,C1,going_up, -x_1 + t0_1 >= 0, -g2 + y >= 0, -y + g1 >= 0, c0 - z >= 0)), And(in_1, far_0, C1, is_up, c1 - z == 0, -x_1 + t2_1 >= 0, -c1 + c0 >= 0), And(near_1,far_0,C2,is_down, -x_1 + t0_1 >= 0, -x_1 + t2_1 >= 0, x_1 - t1_1 >= 0), And(far_1, far_0, C0, is_up), And(far_1,near_0,C1,going_up, -x_0 + t2_0 >= 0, -x_0 + t0_0 >= 0, -y + g1 >= 0, c0 - z >= 0, x_0 - t1_0 >= 0), And(in_1, far_0, C2, coming_down, -x_1 + t2_1 >= 0, -y + g0 >= 0), And(far_1, far_0, C0, is_up), And(And(far_1,near_0,C1,going_up, -x_0 + t0_0 >= 0, -y + g1 >= 0, c0 - z >= 0), And(far_1,near_0,C1,going_up, -x_0 + t0_0 >= 0, -g2 + y >= 0, -y + g1 >= 0, c0 - z >= 0)), And(And(far_1,near_0,C2,coming_down, -x_0 + t0_0 >= 0, -y + g0 >= 0), And(far_1,near_0,C2,coming_down, -x_0 + t0_0 >= 0, -g2 + y >= 0, -y + g0 >= 0)), And(near_1,far_0,C1,is_up, -x_1 + t0_1 >= 0, -x_1 + t2_1 >= 0, c0 - z >= 0, x_1 - t1_1 >= 0), And(near_1,far_0,C2,coming_down, -x_1 + t0_1 >= 0, -x_1 + t2_1 >= 0, -y + g0 >= 0, x_1 - t1_1 >= 0), And(And(in_1,far_0,C2,coming_down, -x_1 + t2_1 >= 0, -y + g0 >= 0), And(in_1,far_0,C2,coming_down, -x_1 + t2_1 >= 0, -g2 + y >= 0, -y + g0 >= 0)), And(And(far_1,in_0,C2,coming_down, -x_0 + t2_0 >= 0, -y + g0 >= 0), And(far_1,in_0,C2,coming_down, -x_0 + t2_0 >= 0, -g2 + y >= 0, -y + g0 >= 0)), And(far_1,near_0,C2,is_down, -x_0 + t2_0 >= 0, -x_0 + t0_0 >= 0, x_0 - t1_0 >= 0), And(far_1, in_0, C2, coming_down, -x_0 + t2_0 >= 0, -y + g0 >= 0))

DisN = Not(En)

NewCond = True
NotAt2Locs_all = And(NotAt2Locs_train_1hh, NotAt2Locs_train_0hh, NotAt2Locs_controllerhh, NotAt2Locs_gatehh)
PosClks = And(t1_1 >= 0, het_1 >= 0, hat_1 >= 0, t2_1 >= 0, hepst_1 >= 0, x_1 >= 0, t0_1 >= 0, hepst_0 >= 0, hat_0 >= 0, t1_0 >= 0, t2_0 >= 0, het_0 >= 0, x_0 >= 0, t0_0 >= 0, hac >= 0, hrc >= 0, c2 >= 0, hlc >= 0, c1 >= 0, hec >= 0, c0 >= 0, z >= 0, y >= 0, g2 >= 0, g1 >= 0, hepsg >= 0, g0 >= 0, hlg >= 0, hrg >= 0)
Kp_all = And(Kp_train_1hh, Kp_train_0hh, Kp_controllerhh, Kp_gatehh)
AddInvs = And(absReachII, NewCond, PosClks, NotAt2Locs_all)
Gi = And(citrain_1hh, citrain_0hh, cicontrollerhh, cigatehh, AddInvs)

hrcrg, hacat_1, hacat_0, hecet_0, hlclg, hepsg, hepst_1, hecet_1, hepst_0 = Ints('hrcrg hacat_1 hacat_0 hecet_0 hlclg hepsg hepst_1 hecet_1 hepst_0')
PosHClks = And(hrcrg >= 0, hacat_1 >= 0, hacat_0 >= 0, hecet_0 >= 0, hlclg >= 0, hepsg >= 0, hepst_1 >= 0, hecet_1 >= 0, hepst_0 >= 0)
EqsS = And(And(And(hlc == hlg, Or(And(hec == het_0, hec <= het_1), And(hec == het_1, hec <= het_0))), Or(And(hac == hat_1, hac <= hat_0), And(hac == hat_0, hac <= hat_1))), hrc == hrg)
Gih = And(citrain_1hh, citrain_0hh, cicontrollerhh, cigatehh, EqsS, AddInvs, PosHClks )
dead = And(Gih, DisN)
EqsC = And(hlg == hlclg, hrg == hrcrg, hat_1 == hacat_1, Or(And(hec == hecet_0, hecet_0 <= hecet_1), And(hec == hecet_1, hecet_1 <= hecet_0)), Or(And(hac == hacat_0, hacat_0 <= hacat_1), And(hac == hacat_1, hacat_1 <= hacat_0)), hrc == hrcrg, hepsg == hepsg, het_0 == hecet_0, hepst_1 == hepst_1, hlc == hlclg, hepst_0 == hepst_0, hat_0 == hacat_0, het_1 == hecet_1)
Sep = And(Or(hecet_0 - hecet_1 >= 0, hecet_1 - hecet_0 >= 0), Or(hacat_0 - hacat_1 >= 0, hacat_1 - hacat_0 >= 0))
GihExt = And(citrain_1hh, citrain_0hh, cicontrollerhh, cigatehh, EqsS, EqsC, Sep, AddInvs )
deadExt = And(GihExt, DisN)
print "Solving deadExt:" 
getCEX(deadExt)



safe = True
#Solving EF formula: 
EFformula = Exists([t1_1,t2_1,g2,c2,t1_0,g1,c1,t2_0,g0,c0,t0_1,t0_0], And(Kp_all, ForAll([far_1, near_1, in_1, far_0, near_0, in_0, C0, C1, C2, C3, is_up, coming_down, is_down, going_up, het_1, hac, hepst_0, hat_1, hrc, y, hepst_1, hat_0, x_1, hlc, hepsg, hec, het_0, x_0, hlg, hrg, z, hrcrg, hacat_1, hacat_0, hecet_0, hlclg, hepsg, hepst_1, hecet_1, hepst_0], Implies(Gih, And(safe, En)))))
s = Solver() 
s.add(EFformula) 
print s.check() 
print s.model()