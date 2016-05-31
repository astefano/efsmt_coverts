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



l0_16, l1_16 = Bools('l0_16 l1_16')
l0_9, l1_9 = Bools('l0_9 l1_9')
l0_10, l1_10 = Bools('l0_10 l1_10')
l0_4, l1_4 = Bools('l0_4 l1_4')
l0_11, l1_11 = Bools('l0_11 l1_11')
lc0, lc1 = Bools('lc0 lc1')
l0_8, l1_8 = Bools('l0_8 l1_8')
l0_5, l1_5 = Bools('l0_5 l1_5')
l0_3, l1_3 = Bools('l0_3 l1_3')
l0_15, l1_15 = Bools('l0_15 l1_15')
l0_14, l1_14 = Bools('l0_14 l1_14')
l0_0, l1_0 = Bools('l0_0 l1_0')
l0_13, l1_13 = Bools('l0_13 l1_13')
l0_6, l1_6 = Bools('l0_6 l1_6')
l0_1, l1_1 = Bools('l0_1 l1_1')
l0_7, l1_7 = Bools('l0_7 l1_7')
l0_2, l1_2 = Bools('l0_2 l1_2')
l0_12, l1_12 = Bools('l0_12 l1_12')
hcool_16, hrest_16, x_16, ct = Ints('hcool_16 hrest_16 x_16 ct')
hcool_9, ct, hrest_9, x_9 = Ints('hcool_9 ct hrest_9 x_9')
x_10, hrest_10, ct, hcool_10 = Ints('x_10 hrest_10 ct hcool_10')
hcool_4, hrest_4, x_4, ct = Ints('hcool_4 hrest_4 x_4 ct')
hrest_11, ct, hcool_11, x_11 = Ints('hrest_11 ct hcool_11 x_11')
p, hrestc, hcoolc, xc = Ints('p hrestc hcoolc xc')
hcool_8, hrest_8, ct, x_8 = Ints('hcool_8 hrest_8 ct x_8')
hrest_5, ct, hcool_5, x_5 = Ints('hrest_5 ct hcool_5 x_5')
hcool_3, ct, hrest_3, x_3 = Ints('hcool_3 ct hrest_3 x_3')
x_15, hrest_15, hcool_15, ct = Ints('x_15 hrest_15 hcool_15 ct')
hcool_14, ct, hrest_14, x_14 = Ints('hcool_14 ct hrest_14 x_14')
hcool_0, hrest_0, x_0, ct = Ints('hcool_0 hrest_0 x_0 ct')
ct, hcool_13, hrest_13, x_13 = Ints('ct hcool_13 hrest_13 x_13')
x_6, hcool_6, ct, hrest_6 = Ints('x_6 hcool_6 ct hrest_6')
ct, hcool_1, hrest_1, x_1 = Ints('ct hcool_1 hrest_1 x_1')
hcool_7, hrest_7, x_7, ct = Ints('hcool_7 hrest_7 x_7 ct')
x_2, hcool_2, hrest_2, ct = Ints('x_2 hcool_2 hrest_2 ct')
ct, hcool_12, hrest_12, x_12 = Ints('ct hcool_12 hrest_12 x_12')



















ciRod_16hh = Or(And(l0_16,  hrest_16 >= 0,  x_16 == hrest_16,  hcool_16 == hrest_16), And(l1_16,  x_16 >= hcool_16,  hcool_16 >= 0,  x_16 >= ct + hcool_16,  x_16 == hrest_16), And(l0_16,  hcool_16 >= hrest_16,  hrest_16 >= 0,  x_16 == hrest_16))

NotAt2Locs_Rod_16hh  = Not(And(l0_16, l1_16))

Kp_Rod_16hh = And(Tactic('qe2').apply(Exists([x_16,hcool_16,hrest_16], And( hrest_16 >= 0, x_16 == hrest_16, hcool_16 == hrest_16))).as_expr(), Tactic('qe2').apply(Exists([x_16,hcool_16,hrest_16], And( x_16 >= hcool_16, hcool_16 >= 0, x_16 >= ct + hcool_16, x_16 == hrest_16))).as_expr())

ciRod_9hh = Or(And(l0_9,  hrest_9 >= 0,  x_9 == hrest_9,  hcool_9 == hrest_9), And(l1_9,  x_9 >= hcool_9,  hcool_9 >= 0,  x_9 >= ct + hcool_9,  x_9 == hrest_9), And(l0_9,  hcool_9 >= hrest_9,  hrest_9 >= 0,  x_9 == hrest_9))

NotAt2Locs_Rod_9hh  = Not(And(l0_9, l1_9))

Kp_Rod_9hh = And(Tactic('qe2').apply(Exists([x_9,hcool_9,hrest_9], And( hrest_9 >= 0, x_9 == hrest_9, hcool_9 == hrest_9))).as_expr(), Tactic('qe2').apply(Exists([x_9,hcool_9,hrest_9], And( x_9 >= hcool_9, hcool_9 >= 0, x_9 >= ct + hcool_9, x_9 == hrest_9))).as_expr())

ciRod_10hh = Or(And(l0_10,  hrest_10 >= 0,  x_10 == hrest_10,  hcool_10 == hrest_10), And(l1_10,  x_10 >= hcool_10,  hcool_10 >= 0,  x_10 >= ct + hcool_10,  x_10 == hrest_10), And(l0_10,  hcool_10 >= hrest_10,  hrest_10 >= 0,  x_10 == hrest_10))

NotAt2Locs_Rod_10hh  = Not(And(l0_10, l1_10))

Kp_Rod_10hh = And(Tactic('qe2').apply(Exists([x_10,hcool_10,hrest_10], And( hrest_10 >= 0, x_10 == hrest_10, hcool_10 == hrest_10))).as_expr(), Tactic('qe2').apply(Exists([x_10,hcool_10,hrest_10], And( x_10 >= hcool_10, hcool_10 >= 0, x_10 >= ct + hcool_10, x_10 == hrest_10))).as_expr())

ciRod_4hh = Or(And(l0_4,  hrest_4 >= 0,  x_4 == hrest_4,  hcool_4 == hrest_4), And(l1_4,  x_4 >= hcool_4,  hcool_4 >= 0,  x_4 >= ct + hcool_4,  x_4 == hrest_4), And(l0_4,  hcool_4 >= hrest_4,  hrest_4 >= 0,  x_4 == hrest_4))

NotAt2Locs_Rod_4hh  = Not(And(l0_4, l1_4))

Kp_Rod_4hh = And(Tactic('qe2').apply(Exists([x_4,hcool_4,hrest_4], And( hrest_4 >= 0, x_4 == hrest_4, hcool_4 == hrest_4))).as_expr(), Tactic('qe2').apply(Exists([x_4,hcool_4,hrest_4], And( x_4 >= hcool_4, hcool_4 >= 0, x_4 >= ct + hcool_4, x_4 == hrest_4))).as_expr())

ciRod_11hh = Or(And(l0_11,  hrest_11 >= 0,  x_11 == hrest_11,  hcool_11 == hrest_11), And(l1_11,  x_11 >= hcool_11,  hcool_11 >= 0,  x_11 >= ct + hcool_11,  x_11 == hrest_11), And(l0_11,  hcool_11 >= hrest_11,  hrest_11 >= 0,  x_11 == hrest_11))

NotAt2Locs_Rod_11hh  = Not(And(l0_11, l1_11))

Kp_Rod_11hh = And(Tactic('qe2').apply(Exists([x_11,hcool_11,hrest_11], And( hrest_11 >= 0, x_11 == hrest_11, hcool_11 == hrest_11))).as_expr(), Tactic('qe2').apply(Exists([x_11,hcool_11,hrest_11], And( x_11 >= hcool_11, hcool_11 >= 0, x_11 >= ct + hcool_11, x_11 == hrest_11))).as_expr())

cicontrollerhh = Or(And(lc0,  900 >= xc,  xc >= 0,  xc == hcoolc,  xc == hrestc), And(lc1,  450 >= xc,  xc >= 0,  xc == hcoolc,  xc + 900 == hrestc), And(lc0,  900 >= xc,  xc >= 0,  xc + 450 == hcoolc,  xc == hrestc))

NotAt2Locs_controllerhh  = Not(And(lc0, lc1))

Kp_controllerhh = And(Tactic('qe2').apply(Exists([xc,hcoolc,hrestc], And( 900 >= xc, xc >= 0, xc == hcoolc, xc == hrestc))).as_expr(), Tactic('qe2').apply(Exists([xc,hcoolc,hrestc], And( 450 >= xc, xc >= 0, xc == hcoolc, xc + 900 == hrestc))).as_expr())

ciRod_8hh = Or(And(l0_8,  hrest_8 >= 0,  x_8 == hrest_8,  hcool_8 == hrest_8), And(l1_8,  x_8 >= hcool_8,  hcool_8 >= 0,  x_8 >= ct + hcool_8,  x_8 == hrest_8), And(l0_8,  hcool_8 >= hrest_8,  hrest_8 >= 0,  x_8 == hrest_8))

NotAt2Locs_Rod_8hh  = Not(And(l0_8, l1_8))

Kp_Rod_8hh = And(Tactic('qe2').apply(Exists([x_8,hcool_8,hrest_8], And( hrest_8 >= 0, x_8 == hrest_8, hcool_8 == hrest_8))).as_expr(), Tactic('qe2').apply(Exists([x_8,hcool_8,hrest_8], And( x_8 >= hcool_8, hcool_8 >= 0, x_8 >= ct + hcool_8, x_8 == hrest_8))).as_expr())

ciRod_5hh = Or(And(l0_5,  hrest_5 >= 0,  x_5 == hrest_5,  hcool_5 == hrest_5), And(l1_5,  x_5 >= hcool_5,  hcool_5 >= 0,  x_5 >= ct + hcool_5,  x_5 == hrest_5), And(l0_5,  hcool_5 >= hrest_5,  hrest_5 >= 0,  x_5 == hrest_5))

NotAt2Locs_Rod_5hh  = Not(And(l0_5, l1_5))

Kp_Rod_5hh = And(Tactic('qe2').apply(Exists([x_5,hcool_5,hrest_5], And( hrest_5 >= 0, x_5 == hrest_5, hcool_5 == hrest_5))).as_expr(), Tactic('qe2').apply(Exists([x_5,hcool_5,hrest_5], And( x_5 >= hcool_5, hcool_5 >= 0, x_5 >= ct + hcool_5, x_5 == hrest_5))).as_expr())

ciRod_3hh = Or(And(l0_3,  hrest_3 >= 0,  x_3 == hrest_3,  hcool_3 == hrest_3), And(l1_3,  x_3 >= hcool_3,  hcool_3 >= 0,  x_3 >= ct + hcool_3,  x_3 == hrest_3), And(l0_3,  hcool_3 >= hrest_3,  hrest_3 >= 0,  x_3 == hrest_3))

NotAt2Locs_Rod_3hh  = Not(And(l0_3, l1_3))

Kp_Rod_3hh = And(Tactic('qe2').apply(Exists([x_3,hcool_3,hrest_3], And( hrest_3 >= 0, x_3 == hrest_3, hcool_3 == hrest_3))).as_expr(), Tactic('qe2').apply(Exists([x_3,hcool_3,hrest_3], And( x_3 >= hcool_3, hcool_3 >= 0, x_3 >= ct + hcool_3, x_3 == hrest_3))).as_expr())

ciRod_15hh = Or(And(l0_15,  hrest_15 >= 0,  x_15 == hrest_15,  hcool_15 == hrest_15), And(l1_15,  x_15 >= hcool_15,  hcool_15 >= 0,  x_15 >= ct + hcool_15,  x_15 == hrest_15), And(l0_15,  hcool_15 >= hrest_15,  hrest_15 >= 0,  x_15 == hrest_15))

NotAt2Locs_Rod_15hh  = Not(And(l0_15, l1_15))

Kp_Rod_15hh = And(Tactic('qe2').apply(Exists([x_15,hcool_15,hrest_15], And( hrest_15 >= 0, x_15 == hrest_15, hcool_15 == hrest_15))).as_expr(), Tactic('qe2').apply(Exists([x_15,hcool_15,hrest_15], And( x_15 >= hcool_15, hcool_15 >= 0, x_15 >= ct + hcool_15, x_15 == hrest_15))).as_expr())

ciRod_14hh = Or(And(l0_14,  hrest_14 >= 0,  x_14 == hrest_14,  hcool_14 == hrest_14), And(l1_14,  x_14 >= hcool_14,  hcool_14 >= 0,  x_14 >= ct + hcool_14,  x_14 == hrest_14), And(l0_14,  hcool_14 >= hrest_14,  hrest_14 >= 0,  x_14 == hrest_14))

NotAt2Locs_Rod_14hh  = Not(And(l0_14, l1_14))

Kp_Rod_14hh = And(Tactic('qe2').apply(Exists([x_14,hcool_14,hrest_14], And( hrest_14 >= 0, x_14 == hrest_14, hcool_14 == hrest_14))).as_expr(), Tactic('qe2').apply(Exists([x_14,hcool_14,hrest_14], And( x_14 >= hcool_14, hcool_14 >= 0, x_14 >= ct + hcool_14, x_14 == hrest_14))).as_expr())

ciRod_0hh = Or(And(l0_0,  hrest_0 >= 0,  x_0 == hrest_0,  hcool_0 == hrest_0), And(l1_0,  x_0 >= hcool_0,  hcool_0 >= 0,  x_0 >= ct + hcool_0,  x_0 == hrest_0), And(l0_0,  hcool_0 >= hrest_0,  hrest_0 >= 0,  x_0 == hrest_0))

NotAt2Locs_Rod_0hh  = Not(And(l0_0, l1_0))

Kp_Rod_0hh = And(Tactic('qe2').apply(Exists([x_0,hcool_0,hrest_0], And( hrest_0 >= 0, x_0 == hrest_0, hcool_0 == hrest_0))).as_expr(), Tactic('qe2').apply(Exists([x_0,hcool_0,hrest_0], And( x_0 >= hcool_0, hcool_0 >= 0, x_0 >= ct + hcool_0, x_0 == hrest_0))).as_expr())

ciRod_13hh = Or(And(l0_13,  hrest_13 >= 0,  x_13 == hrest_13,  hcool_13 == hrest_13), And(l1_13,  x_13 >= hcool_13,  hcool_13 >= 0,  x_13 >= ct + hcool_13,  x_13 == hrest_13), And(l0_13,  hcool_13 >= hrest_13,  hrest_13 >= 0,  x_13 == hrest_13))

NotAt2Locs_Rod_13hh  = Not(And(l0_13, l1_13))

Kp_Rod_13hh = And(Tactic('qe2').apply(Exists([x_13,hcool_13,hrest_13], And( hrest_13 >= 0, x_13 == hrest_13, hcool_13 == hrest_13))).as_expr(), Tactic('qe2').apply(Exists([x_13,hcool_13,hrest_13], And( x_13 >= hcool_13, hcool_13 >= 0, x_13 >= ct + hcool_13, x_13 == hrest_13))).as_expr())

ciRod_6hh = Or(And(l0_6,  hrest_6 >= 0,  x_6 == hrest_6,  hcool_6 == hrest_6), And(l1_6,  x_6 >= hcool_6,  hcool_6 >= 0,  x_6 >= ct + hcool_6,  x_6 == hrest_6), And(l0_6,  hcool_6 >= hrest_6,  hrest_6 >= 0,  x_6 == hrest_6))

NotAt2Locs_Rod_6hh  = Not(And(l0_6, l1_6))

Kp_Rod_6hh = And(Tactic('qe2').apply(Exists([x_6,hcool_6,hrest_6], And( hrest_6 >= 0, x_6 == hrest_6, hcool_6 == hrest_6))).as_expr(), Tactic('qe2').apply(Exists([x_6,hcool_6,hrest_6], And( x_6 >= hcool_6, hcool_6 >= 0, x_6 >= ct + hcool_6, x_6 == hrest_6))).as_expr())

ciRod_1hh = Or(And(l0_1,  hrest_1 >= 0,  x_1 == hrest_1,  hcool_1 == hrest_1), And(l1_1,  x_1 >= hcool_1,  hcool_1 >= 0,  x_1 >= ct + hcool_1,  x_1 == hrest_1), And(l0_1,  hcool_1 >= hrest_1,  hrest_1 >= 0,  x_1 == hrest_1))

NotAt2Locs_Rod_1hh  = Not(And(l0_1, l1_1))

Kp_Rod_1hh = And(Tactic('qe2').apply(Exists([x_1,hcool_1,hrest_1], And( hrest_1 >= 0, x_1 == hrest_1, hcool_1 == hrest_1))).as_expr(), Tactic('qe2').apply(Exists([x_1,hcool_1,hrest_1], And( x_1 >= hcool_1, hcool_1 >= 0, x_1 >= ct + hcool_1, x_1 == hrest_1))).as_expr())

ciRod_7hh = Or(And(l0_7,  hrest_7 >= 0,  x_7 == hrest_7,  hcool_7 == hrest_7), And(l1_7,  x_7 >= hcool_7,  hcool_7 >= 0,  x_7 >= ct + hcool_7,  x_7 == hrest_7), And(l0_7,  hcool_7 >= hrest_7,  hrest_7 >= 0,  x_7 == hrest_7))

NotAt2Locs_Rod_7hh  = Not(And(l0_7, l1_7))

Kp_Rod_7hh = And(Tactic('qe2').apply(Exists([x_7,hcool_7,hrest_7], And( hrest_7 >= 0, x_7 == hrest_7, hcool_7 == hrest_7))).as_expr(), Tactic('qe2').apply(Exists([x_7,hcool_7,hrest_7], And( x_7 >= hcool_7, hcool_7 >= 0, x_7 >= ct + hcool_7, x_7 == hrest_7))).as_expr())

ciRod_2hh = Or(And(l0_2,  hrest_2 >= 0,  x_2 == hrest_2,  hcool_2 == hrest_2), And(l1_2,  x_2 >= hcool_2,  hcool_2 >= 0,  x_2 >= ct + hcool_2,  x_2 == hrest_2), And(l0_2,  hcool_2 >= hrest_2,  hrest_2 >= 0,  x_2 == hrest_2))

NotAt2Locs_Rod_2hh  = Not(And(l0_2, l1_2))

Kp_Rod_2hh = And(Tactic('qe2').apply(Exists([x_2,hcool_2,hrest_2], And( hrest_2 >= 0, x_2 == hrest_2, hcool_2 == hrest_2))).as_expr(), Tactic('qe2').apply(Exists([x_2,hcool_2,hrest_2], And( x_2 >= hcool_2, hcool_2 >= 0, x_2 >= ct + hcool_2, x_2 == hrest_2))).as_expr())

ciRod_12hh = Or(And(l0_12,  hrest_12 >= 0,  x_12 == hrest_12,  hcool_12 == hrest_12), And(l1_12,  x_12 >= hcool_12,  hcool_12 >= 0,  x_12 >= ct + hcool_12,  x_12 == hrest_12), And(l0_12,  hcool_12 >= hrest_12,  hrest_12 >= 0,  x_12 == hrest_12))

NotAt2Locs_Rod_12hh  = Not(And(l0_12, l1_12))

Kp_Rod_12hh = And(Tactic('qe2').apply(Exists([x_12,hcool_12,hrest_12], And( hrest_12 >= 0, x_12 == hrest_12, hcool_12 == hrest_12))).as_expr(), Tactic('qe2').apply(Exists([x_12,hcool_12,hrest_12], And( x_12 >= hcool_12, hcool_12 >= 0, x_12 >= ct + hcool_12, x_12 == hrest_12))).as_expr())


#abstract reach
absReachII = Or(And(l0_16, l0_9, l0_10, l0_4, l0_11, lc0, l0_8, l0_5, l0_3, l0_15, l0_14, l0_0, l0_13, l0_6, l0_1, l0_7, l0_2, l0_12), And(l0_16, l0_9, l0_10, l0_4, l0_11, lc0, l0_8, l0_5, l0_3, l0_15, l0_14, l0_0, l0_13, l0_6, l0_1, l0_7, l0_2, l0_12), And(l0_16, l0_9, l0_10, l0_4, l0_11, lc0, l0_8, l0_5, l0_3, l0_15, l0_14, l0_0, l0_13, l0_6, l0_1, l0_7, l0_2, l0_12), And(l0_16, l0_9, l0_10, l0_4, l0_11, lc0, l0_8, l0_5, l0_3, l0_15, l0_14, l0_0, l0_13, l0_6, l0_1, l0_7, l0_2, l0_12), And(l0_16, l0_9, l0_10, l0_4, l0_11, lc0, l0_8, l0_5, l0_3, l0_15, l0_14, l0_0, l0_13, l0_6, l0_1, l0_7, l0_2, l0_12), And(l0_16, l0_9, l0_10, l0_4, l0_11, lc0, l0_8, l0_5, l0_3, l0_15, l0_14, l0_0, l0_13, l0_6, l0_1, l0_7, l0_2, l0_12), And(l0_16, l0_9, l0_10, l0_4, l0_11, lc0, l0_8, l0_5, l0_3, l0_15, l0_14, l0_0, l0_13, l0_6, l0_1, l0_7, l0_2, l0_12), And(l0_16, l0_9, l0_10, l0_4, l0_11, lc0, l0_8, l0_5, l0_3, l0_15, l0_14, l0_0, l0_13, l0_6, l0_1, l0_7, l0_2, l0_12), And(l0_16, l0_9, l0_10, l0_4, l0_11, lc0, l0_8, l0_5, l0_3, l0_15, l0_14, l0_0, l0_13, l0_6, l0_1, l0_7, l0_2, l0_12), And(l0_16, l0_9, l0_10, l0_4, l0_11, lc0, l0_8, l0_5, l0_3, l0_15, l0_14, l0_0, l0_13, l0_6, l0_1, l0_7, l0_2, l0_12), And(l0_16, l0_9, l0_10, l0_4, l0_11, lc0, l0_8, l0_5, l0_3, l0_15, l0_14, l0_0, l0_13, l0_6, l0_1, l0_7, l0_2, l0_12), And(l0_16, l0_9, l0_10, l0_4, l0_11, lc0, l0_8, l0_5, l0_3, l0_15, l0_14, l0_0, l0_13, l0_6, l0_1, l0_7, l0_2, l0_12), And(l0_16, l0_9, l0_10, l0_4, l0_11, lc0, l0_8, l0_5, l0_3, l0_15, l0_14, l0_0, l0_13, l0_6, l0_1, l0_7, l0_2, l0_12), And(l0_16, l0_9, l0_10, l0_4, l0_11, lc1, l0_8, l0_5, l0_3, l0_15, l0_14, l1_0, l0_13, l0_6, l0_1, l0_7, l0_2, l0_12), And(l0_16, l0_9, l0_10, l0_4, l0_11, lc0, l0_8, l0_5, l0_3, l0_15, l0_14, l0_0, l0_13, l0_6, l0_1, l0_7, l0_2, l0_12), And(l0_16, l0_9, l0_10, l0_4, l0_11, lc0, l0_8, l0_5, l0_3, l0_15, l0_14, l0_0, l0_13, l0_6, l0_1, l0_7, l0_2, l0_12), And(l0_16, l0_9, l0_10, l0_4, l0_11, lc0, l0_8, l0_5, l0_3, l0_15, l0_14, l0_0, l0_13, l0_6, l0_1, l0_7, l0_2, l0_12)) 

#Enabled guided by absReach
En = Or(And(l0_16, l0_9, l0_10, l0_4, l0_11, lc0, l0_8, l0_5, l0_3, l0_15, l0_14, l0_0, l0_13, l0_6, l0_1, l0_7, l0_2, l0_12, -xc >= -900, x_8 - ct >= 0), And(l0_16, l0_9, l0_10, l0_4, l0_11, lc0, l0_8, l0_5, l0_3, l0_15, l0_14, l0_0, l0_13, l0_6, l0_1, l0_7, l0_2, l0_12, -xc >= -900, x_10 - ct >= 0), And(l0_16, l0_9, l0_10, l0_4, l0_11, lc0, l0_8, l0_5, l0_3, l0_15, l0_14, l0_0, l0_13, l0_6, l0_1, l0_7, l0_2, l0_12, -xc >= -900, -ct + x_12 >= 0), And(l0_16, l0_9, l0_10, l0_4, l0_11, lc0, l0_8, l0_5, l0_3, l0_15, l0_14, l0_0, l0_13, l0_6, l0_1, l0_7, l0_2, l0_12, -xc >= -900, -ct + x_2 >= 0), And(l0_16, l0_9, l0_10, l0_4, l0_11, lc0, l0_8, l0_5, l0_3, l0_15, l0_14, l0_0, l0_13, l0_6, l0_1, l0_7, l0_2, l0_12, -xc >= -900, x_13 - ct >= 0), And(l0_16, l0_9, l0_10, l0_4, l0_11, lc0, l0_8, l0_5, l0_3, l0_15, l0_14, l0_0, l0_13, l0_6, l0_1, l0_7, l0_2, l0_12, -xc >= -900, -ct + x_1 >= 0), And(l0_16, l0_9, l0_10, l0_4, l0_11, lc0, l0_8, l0_5, l0_3, l0_15, l0_14, l0_0, l0_13, l0_6, l0_1, l0_7, l0_2, l0_12, -xc >= -900, x_4 - ct >= 0), And(l0_16, l0_9, l0_10, l0_4, l0_11, lc0, l0_8, l0_5, l0_3, l0_15, l0_14, l0_0, l0_13, l0_6, l0_1, l0_7, l0_2, l0_12, -xc >= -900, x_14 - ct >= 0), And(l0_16, l0_9, l0_10, l0_4, l0_11, lc0, l0_8, l0_5, l0_3, l0_15, l0_14, l0_0, l0_13, l0_6, l0_1, l0_7, l0_2, l0_12, -xc >= -900, x_0 - ct >= 0), And(l0_16, l0_9, l0_10, l0_4, l0_11, lc0, l0_8, l0_5, l0_3, l0_15, l0_14, l0_0, l0_13, l0_6, l0_1, l0_7, l0_2, l0_12, -xc >= -900, -ct + x_7 >= 0), And(l0_16, l0_9, l0_10, l0_4, l0_11, lc0, l0_8, l0_5, l0_3, l0_15, l0_14, l0_0, l0_13, l0_6, l0_1, l0_7, l0_2, l0_12, -xc >= -900, x_11 - ct >= 0), And(l0_16, l0_9, l0_10, l0_4, l0_11, lc0, l0_8, l0_5, l0_3, l0_15, l0_14, l0_0, l0_13, l0_6, l0_1, l0_7, l0_2, l0_12, -xc >= -900, x_15 - ct >= 0), And(l0_16, l0_9, l0_10, l0_4, l0_11, lc0, l0_8, l0_5, l0_3, l0_15, l0_14, l0_0, l0_13, l0_6, l0_1, l0_7, l0_2, l0_12, -xc >= -900, x_9 - ct >= 0), And(l0_16, l0_9, l0_10, l0_4, l0_11, lc1, l0_8, l0_5, l0_3, l0_15, l0_14, l1_0, l0_13, l0_6, l0_1, l0_7, l0_2, l0_12, -xc >= -450), And(l0_16, l0_9, l0_10, l0_4, l0_11, lc0, l0_8, l0_5, l0_3, l0_15, l0_14, l0_0, l0_13, l0_6, l0_1, l0_7, l0_2, l0_12, -xc >= -900, -ct + x_6 >= 0), And(l0_16, l0_9, l0_10, l0_4, l0_11, lc0, l0_8, l0_5, l0_3, l0_15, l0_14, l0_0, l0_13, l0_6, l0_1, l0_7, l0_2, l0_12, -xc >= -900, -ct + x_3 >= 0), And(l0_16, l0_9, l0_10, l0_4, l0_11, lc0, l0_8, l0_5, l0_3, l0_15, l0_14, l0_0, l0_13, l0_6, l0_1, l0_7, l0_2, l0_12, -xc >= -900, x_5 - ct >= 0))

DisN = Not(En)

NewCond = True
NotAt2Locs_all = And(NotAt2Locs_Rod_16hh, NotAt2Locs_Rod_9hh, NotAt2Locs_Rod_10hh, NotAt2Locs_Rod_4hh, NotAt2Locs_Rod_11hh, NotAt2Locs_controllerhh, NotAt2Locs_Rod_8hh, NotAt2Locs_Rod_5hh, NotAt2Locs_Rod_3hh, NotAt2Locs_Rod_15hh, NotAt2Locs_Rod_14hh, NotAt2Locs_Rod_0hh, NotAt2Locs_Rod_13hh, NotAt2Locs_Rod_6hh, NotAt2Locs_Rod_1hh, NotAt2Locs_Rod_7hh, NotAt2Locs_Rod_2hh, NotAt2Locs_Rod_12hh)
PosClks = And(hcool_16 >= 0, hrest_16 >= 0, x_16 >= 0, ct >= 0, hcool_9 >= 0, ct >= 0, hrest_9 >= 0, x_9 >= 0, x_10 >= 0, hrest_10 >= 0, ct >= 0, hcool_10 >= 0, hcool_4 >= 0, hrest_4 >= 0, x_4 >= 0, ct >= 0, hrest_11 >= 0, ct >= 0, hcool_11 >= 0, x_11 >= 0, p >= 0, hrestc >= 0, hcoolc >= 0, xc >= 0, hcool_8 >= 0, hrest_8 >= 0, ct >= 0, x_8 >= 0, hrest_5 >= 0, ct >= 0, hcool_5 >= 0, x_5 >= 0, hcool_3 >= 0, ct >= 0, hrest_3 >= 0, x_3 >= 0, x_15 >= 0, hrest_15 >= 0, hcool_15 >= 0, ct >= 0, hcool_14 >= 0, ct >= 0, hrest_14 >= 0, x_14 >= 0, hcool_0 >= 0, hrest_0 >= 0, x_0 >= 0, ct >= 0, ct >= 0, hcool_13 >= 0, hrest_13 >= 0, x_13 >= 0, x_6 >= 0, hcool_6 >= 0, ct >= 0, hrest_6 >= 0, ct >= 0, hcool_1 >= 0, hrest_1 >= 0, x_1 >= 0, hcool_7 >= 0, hrest_7 >= 0, x_7 >= 0, ct >= 0, x_2 >= 0, hcool_2 >= 0, hrest_2 >= 0, ct >= 0, ct >= 0, hcool_12 >= 0, hrest_12 >= 0, x_12 >= 0)
Kp_all = And(Kp_Rod_16hh, Kp_Rod_9hh, Kp_Rod_10hh, Kp_Rod_4hh, Kp_Rod_11hh, Kp_controllerhh, Kp_Rod_8hh, Kp_Rod_5hh, Kp_Rod_3hh, Kp_Rod_15hh, Kp_Rod_14hh, Kp_Rod_0hh, Kp_Rod_13hh, Kp_Rod_6hh, Kp_Rod_1hh, Kp_Rod_7hh, Kp_Rod_2hh, Kp_Rod_12hh)
AddInvs = And(absReachII, NewCond, PosClks, NotAt2Locs_all)
Gi = And(ciRod_16hh, ciRod_9hh, ciRod_10hh, ciRod_4hh, ciRod_11hh, cicontrollerhh, ciRod_8hh, ciRod_5hh, ciRod_3hh, ciRod_15hh, ciRod_14hh, ciRod_0hh, ciRod_13hh, ciRod_6hh, ciRod_1hh, ciRod_7hh, ciRod_2hh, ciRod_12hh, AddInvs)

hcoolccool_13, hcoolccool_5, hcoolccool_8, hcoolccool_10, hcoolccool_11, hcoolccool_4, hcoolccool_12, hcoolccool_2, hcoolccool_3, hcoolccool_6, hcoolccool_0, hcoolccool_14, hcoolccool_9, hrestcrest_0, hcoolccool_15, hcoolccool_1, hcoolccool_7 = Ints('hcoolccool_13 hcoolccool_5 hcoolccool_8 hcoolccool_10 hcoolccool_11 hcoolccool_4 hcoolccool_12 hcoolccool_2 hcoolccool_3 hcoolccool_6 hcoolccool_0 hcoolccool_14 hcoolccool_9 hrestcrest_0 hcoolccool_15 hcoolccool_1 hcoolccool_7')
PosHClks = And(hcoolccool_13 >= 0, hcoolccool_5 >= 0, hcoolccool_8 >= 0, hcoolccool_10 >= 0, hcoolccool_11 >= 0, hcoolccool_4 >= 0, hcoolccool_12 >= 0, hcoolccool_2 >= 0, hcoolccool_3 >= 0, hcoolccool_6 >= 0, hcoolccool_0 >= 0, hcoolccool_14 >= 0, hcoolccool_9 >= 0, hrestcrest_0 >= 0, hcoolccool_15 >= 0, hcoolccool_1 >= 0, hcoolccool_7 >= 0)
EqsS = And(hrestc == hrest_0, Or(And(hcoolc == hcool_13, And(hcoolc <= hcool_5, hcoolc <= hcool_8, hcoolc <= hcool_10, hcoolc <= hcool_11, hcoolc <= hcool_4, hcoolc <= hcool_12, hcoolc <= hcool_2, hcoolc <= hcool_3, hcoolc <= hcool_6, hcoolc <= hcool_0, hcoolc <= hcool_14, hcoolc <= hcool_9, hcoolc <= hcool_15, hcoolc <= hcool_1, hcoolc <= hcool_7)), And(hcoolc == hcool_5, And(hcoolc <= hcool_13, hcoolc <= hcool_8, hcoolc <= hcool_10, hcoolc <= hcool_11, hcoolc <= hcool_4, hcoolc <= hcool_12, hcoolc <= hcool_2, hcoolc <= hcool_3, hcoolc <= hcool_6, hcoolc <= hcool_0, hcoolc <= hcool_14, hcoolc <= hcool_9, hcoolc <= hcool_15, hcoolc <= hcool_1, hcoolc <= hcool_7)), And(hcoolc == hcool_8, And(hcoolc <= hcool_13, hcoolc <= hcool_5, hcoolc <= hcool_10, hcoolc <= hcool_11, hcoolc <= hcool_4, hcoolc <= hcool_12, hcoolc <= hcool_2, hcoolc <= hcool_3, hcoolc <= hcool_6, hcoolc <= hcool_0, hcoolc <= hcool_14, hcoolc <= hcool_9, hcoolc <= hcool_15, hcoolc <= hcool_1, hcoolc <= hcool_7)), And(hcoolc == hcool_10, And(hcoolc <= hcool_13, hcoolc <= hcool_5, hcoolc <= hcool_8, hcoolc <= hcool_11, hcoolc <= hcool_4, hcoolc <= hcool_12, hcoolc <= hcool_2, hcoolc <= hcool_3, hcoolc <= hcool_6, hcoolc <= hcool_0, hcoolc <= hcool_14, hcoolc <= hcool_9, hcoolc <= hcool_15, hcoolc <= hcool_1, hcoolc <= hcool_7)), And(hcoolc == hcool_11, And(hcoolc <= hcool_13, hcoolc <= hcool_5, hcoolc <= hcool_8, hcoolc <= hcool_10, hcoolc <= hcool_4, hcoolc <= hcool_12, hcoolc <= hcool_2, hcoolc <= hcool_3, hcoolc <= hcool_6, hcoolc <= hcool_0, hcoolc <= hcool_14, hcoolc <= hcool_9, hcoolc <= hcool_15, hcoolc <= hcool_1, hcoolc <= hcool_7)), And(hcoolc == hcool_4, And(hcoolc <= hcool_13, hcoolc <= hcool_5, hcoolc <= hcool_8, hcoolc <= hcool_10, hcoolc <= hcool_11, hcoolc <= hcool_12, hcoolc <= hcool_2, hcoolc <= hcool_3, hcoolc <= hcool_6, hcoolc <= hcool_0, hcoolc <= hcool_14, hcoolc <= hcool_9, hcoolc <= hcool_15, hcoolc <= hcool_1, hcoolc <= hcool_7)), And(hcoolc == hcool_12, And(hcoolc <= hcool_13, hcoolc <= hcool_5, hcoolc <= hcool_8, hcoolc <= hcool_10, hcoolc <= hcool_11, hcoolc <= hcool_4, hcoolc <= hcool_2, hcoolc <= hcool_3, hcoolc <= hcool_6, hcoolc <= hcool_0, hcoolc <= hcool_14, hcoolc <= hcool_9, hcoolc <= hcool_15, hcoolc <= hcool_1, hcoolc <= hcool_7)), And(hcoolc == hcool_2, And(hcoolc <= hcool_13, hcoolc <= hcool_5, hcoolc <= hcool_8, hcoolc <= hcool_10, hcoolc <= hcool_11, hcoolc <= hcool_4, hcoolc <= hcool_12, hcoolc <= hcool_3, hcoolc <= hcool_6, hcoolc <= hcool_0, hcoolc <= hcool_14, hcoolc <= hcool_9, hcoolc <= hcool_15, hcoolc <= hcool_1, hcoolc <= hcool_7)), And(hcoolc == hcool_3, And(hcoolc <= hcool_13, hcoolc <= hcool_5, hcoolc <= hcool_8, hcoolc <= hcool_10, hcoolc <= hcool_11, hcoolc <= hcool_4, hcoolc <= hcool_12, hcoolc <= hcool_2, hcoolc <= hcool_6, hcoolc <= hcool_0, hcoolc <= hcool_14, hcoolc <= hcool_9, hcoolc <= hcool_15, hcoolc <= hcool_1, hcoolc <= hcool_7)), And(hcoolc == hcool_6, And(hcoolc <= hcool_13, hcoolc <= hcool_5, hcoolc <= hcool_8, hcoolc <= hcool_10, hcoolc <= hcool_11, hcoolc <= hcool_4, hcoolc <= hcool_12, hcoolc <= hcool_2, hcoolc <= hcool_3, hcoolc <= hcool_0, hcoolc <= hcool_14, hcoolc <= hcool_9, hcoolc <= hcool_15, hcoolc <= hcool_1, hcoolc <= hcool_7)), And(hcoolc == hcool_0, And(hcoolc <= hcool_13, hcoolc <= hcool_5, hcoolc <= hcool_8, hcoolc <= hcool_10, hcoolc <= hcool_11, hcoolc <= hcool_4, hcoolc <= hcool_12, hcoolc <= hcool_2, hcoolc <= hcool_3, hcoolc <= hcool_6, hcoolc <= hcool_14, hcoolc <= hcool_9, hcoolc <= hcool_15, hcoolc <= hcool_1, hcoolc <= hcool_7)), And(hcoolc == hcool_14, And(hcoolc <= hcool_13, hcoolc <= hcool_5, hcoolc <= hcool_8, hcoolc <= hcool_10, hcoolc <= hcool_11, hcoolc <= hcool_4, hcoolc <= hcool_12, hcoolc <= hcool_2, hcoolc <= hcool_3, hcoolc <= hcool_6, hcoolc <= hcool_0, hcoolc <= hcool_9, hcoolc <= hcool_15, hcoolc <= hcool_1, hcoolc <= hcool_7)), And(hcoolc == hcool_9, And(hcoolc <= hcool_13, hcoolc <= hcool_5, hcoolc <= hcool_8, hcoolc <= hcool_10, hcoolc <= hcool_11, hcoolc <= hcool_4, hcoolc <= hcool_12, hcoolc <= hcool_2, hcoolc <= hcool_3, hcoolc <= hcool_6, hcoolc <= hcool_0, hcoolc <= hcool_14, hcoolc <= hcool_15, hcoolc <= hcool_1, hcoolc <= hcool_7)), And(hcoolc == hcool_15, And(hcoolc <= hcool_13, hcoolc <= hcool_5, hcoolc <= hcool_8, hcoolc <= hcool_10, hcoolc <= hcool_11, hcoolc <= hcool_4, hcoolc <= hcool_12, hcoolc <= hcool_2, hcoolc <= hcool_3, hcoolc <= hcool_6, hcoolc <= hcool_0, hcoolc <= hcool_14, hcoolc <= hcool_9, hcoolc <= hcool_1, hcoolc <= hcool_7)), And(hcoolc == hcool_1, And(hcoolc <= hcool_13, hcoolc <= hcool_5, hcoolc <= hcool_8, hcoolc <= hcool_10, hcoolc <= hcool_11, hcoolc <= hcool_4, hcoolc <= hcool_12, hcoolc <= hcool_2, hcoolc <= hcool_3, hcoolc <= hcool_6, hcoolc <= hcool_0, hcoolc <= hcool_14, hcoolc <= hcool_9, hcoolc <= hcool_15, hcoolc <= hcool_7)), And(hcoolc == hcool_7, And(hcoolc <= hcool_13, hcoolc <= hcool_5, hcoolc <= hcool_8, hcoolc <= hcool_10, hcoolc <= hcool_11, hcoolc <= hcool_4, hcoolc <= hcool_12, hcoolc <= hcool_2, hcoolc <= hcool_3, hcoolc <= hcool_6, hcoolc <= hcool_0, hcoolc <= hcool_14, hcoolc <= hcool_9, hcoolc <= hcool_15, hcoolc <= hcool_1))))
Gih = And(ciRod_16hh, ciRod_9hh, ciRod_10hh, ciRod_4hh, ciRod_11hh, cicontrollerhh, ciRod_8hh, ciRod_5hh, ciRod_3hh, ciRod_15hh, ciRod_14hh, ciRod_0hh, ciRod_13hh, ciRod_6hh, ciRod_1hh, ciRod_7hh, ciRod_2hh, ciRod_12hh, EqsS, AddInvs, PosHClks )
dead = And(Gih, DisN)
EqsC = And(hcool_2 == hcoolccool_2, hcool_4 == hcoolccool_4, hcool_11 == hcoolccool_11, Or(And(hcoolc == hcoolccool_0, And(hcoolccool_0 <= hcoolccool_13, hcoolccool_0 <= hcoolccool_1, hcoolccool_0 <= hcoolccool_10, hcoolccool_0 <= hcoolccool_6, hcoolccool_0 <= hcoolccool_2, hcoolccool_0 <= hcoolccool_7, hcoolccool_0 <= hcoolccool_14, hcoolccool_0 <= hcoolccool_5, hcoolccool_0 <= hcoolccool_11, hcoolccool_0 <= hcoolccool_4, hcoolccool_0 <= hcoolccool_15, hcoolccool_0 <= hcoolccool_9, hcoolccool_0 <= hcoolccool_3, hcoolccool_0 <= hcoolccool_12, hcoolccool_0 <= hcoolccool_8)), And(hcoolc == hcoolccool_11, And(hcoolccool_11 <= hcoolccool_15, hcoolccool_11 <= hcoolccool_2, hcoolccool_11 <= hcoolccool_6, hcoolccool_11 <= hcoolccool_1, hcoolccool_11 <= hcoolccool_7, hcoolccool_11 <= hcoolccool_3, hcoolccool_11 <= hcoolccool_0, hcoolccool_11 <= hcoolccool_12, hcoolccool_11 <= hcoolccool_8, hcoolccool_11 <= hcoolccool_4, hcoolccool_11 <= hcoolccool_13, hcoolccool_11 <= hcoolccool_10, hcoolccool_11 <= hcoolccool_9, hcoolccool_11 <= hcoolccool_5, hcoolccool_11 <= hcoolccool_14)), And(hcoolc == hcoolccool_2, And(hcoolccool_2 <= hcoolccool_0, hcoolccool_2 <= hcoolccool_3, hcoolccool_2 <= hcoolccool_8, hcoolccool_2 <= hcoolccool_10, hcoolccool_2 <= hcoolccool_9, hcoolccool_2 <= hcoolccool_7, hcoolccool_2 <= hcoolccool_11, hcoolccool_2 <= hcoolccool_6, hcoolccool_2 <= hcoolccool_15, hcoolccool_2 <= hcoolccool_14, hcoolccool_2 <= hcoolccool_12, hcoolccool_2 <= hcoolccool_5, hcoolccool_2 <= hcoolccool_1, hcoolccool_2 <= hcoolccool_13, hcoolccool_2 <= hcoolccool_4)), And(hcoolc == hcoolccool_13, And(hcoolccool_13 <= hcoolccool_4, hcoolccool_13 <= hcoolccool_10, hcoolccool_13 <= hcoolccool_5, hcoolccool_13 <= hcoolccool_1, hcoolccool_13 <= hcoolccool_8, hcoolccool_13 <= hcoolccool_6, hcoolccool_13 <= hcoolccool_9, hcoolccool_13 <= hcoolccool_14, hcoolccool_13 <= hcoolccool_12, hcoolccool_13 <= hcoolccool_2, hcoolccool_13 <= hcoolccool_7, hcoolccool_13 <= hcoolccool_0, hcoolccool_13 <= hcoolccool_11, hcoolccool_13 <= hcoolccool_3, hcoolccool_13 <= hcoolccool_15)), And(hcoolc == hcoolccool_5, And(hcoolccool_5 <= hcoolccool_9, hcoolccool_5 <= hcoolccool_14, hcoolccool_5 <= hcoolccool_10, hcoolccool_5 <= hcoolccool_1, hcoolccool_5 <= hcoolccool_0, hcoolccool_5 <= hcoolccool_13, hcoolccool_5 <= hcoolccool_6, hcoolccool_5 <= hcoolccool_4, hcoolccool_5 <= hcoolccool_7, hcoolccool_5 <= hcoolccool_12, hcoolccool_5 <= hcoolccool_3, hcoolccool_5 <= hcoolccool_8, hcoolccool_5 <= hcoolccool_15, hcoolccool_5 <= hcoolccool_11, hcoolccool_5 <= hcoolccool_2)), And(hcoolc == hcoolccool_4, And(hcoolccool_4 <= hcoolccool_9, hcoolccool_4 <= hcoolccool_5, hcoolccool_4 <= hcoolccool_6, hcoolccool_4 <= hcoolccool_1, hcoolccool_4 <= hcoolccool_12, hcoolccool_4 <= hcoolccool_13, hcoolccool_4 <= hcoolccool_0, hcoolccool_4 <= hcoolccool_3, hcoolccool_4 <= hcoolccool_7, hcoolccool_4 <= hcoolccool_10, hcoolccool_4 <= hcoolccool_15, hcoolccool_4 <= hcoolccool_14, hcoolccool_4 <= hcoolccool_2, hcoolccool_4 <= hcoolccool_8, hcoolccool_4 <= hcoolccool_11)), And(hcoolc == hcoolccool_8, And(hcoolccool_8 <= hcoolccool_14, hcoolccool_8 <= hcoolccool_2, hcoolccool_8 <= hcoolccool_6, hcoolccool_8 <= hcoolccool_5, hcoolccool_8 <= hcoolccool_13, hcoolccool_8 <= hcoolccool_0, hcoolccool_8 <= hcoolccool_9, hcoolccool_8 <= hcoolccool_12, hcoolccool_8 <= hcoolccool_7, hcoolccool_8 <= hcoolccool_1, hcoolccool_8 <= hcoolccool_4, hcoolccool_8 <= hcoolccool_3, hcoolccool_8 <= hcoolccool_11, hcoolccool_8 <= hcoolccool_10, hcoolccool_8 <= hcoolccool_15)), And(hcoolc == hcoolccool_10, And(hcoolccool_10 <= hcoolccool_2, hcoolccool_10 <= hcoolccool_12, hcoolccool_10 <= hcoolccool_3, hcoolccool_10 <= hcoolccool_7, hcoolccool_10 <= hcoolccool_11, hcoolccool_10 <= hcoolccool_1, hcoolccool_10 <= hcoolccool_15, hcoolccool_10 <= hcoolccool_4, hcoolccool_10 <= hcoolccool_8, hcoolccool_10 <= hcoolccool_14, hcoolccool_10 <= hcoolccool_0, hcoolccool_10 <= hcoolccool_9, hcoolccool_10 <= hcoolccool_5, hcoolccool_10 <= hcoolccool_13, hcoolccool_10 <= hcoolccool_6)), And(hcoolc == hcoolccool_15, And(hcoolccool_15 <= hcoolccool_6, hcoolccool_15 <= hcoolccool_2, hcoolccool_15 <= hcoolccool_14, hcoolccool_15 <= hcoolccool_5, hcoolccool_15 <= hcoolccool_10, hcoolccool_15 <= hcoolccool_9, hcoolccool_15 <= hcoolccool_11, hcoolccool_15 <= hcoolccool_3, hcoolccool_15 <= hcoolccool_8, hcoolccool_15 <= hcoolccool_12, hcoolccool_15 <= hcoolccool_4, hcoolccool_15 <= hcoolccool_1, hcoolccool_15 <= hcoolccool_13, hcoolccool_15 <= hcoolccool_7, hcoolccool_15 <= hcoolccool_0)), And(hcoolc == hcoolccool_1, And(hcoolccool_1 <= hcoolccool_2, hcoolccool_1 <= hcoolccool_15, hcoolccool_1 <= hcoolccool_11, hcoolccool_1 <= hcoolccool_6, hcoolccool_1 <= hcoolccool_12, hcoolccool_1 <= hcoolccool_3, hcoolccool_1 <= hcoolccool_4, hcoolccool_1 <= hcoolccool_7, hcoolccool_1 <= hcoolccool_14, hcoolccool_1 <= hcoolccool_10, hcoolccool_1 <= hcoolccool_8, hcoolccool_1 <= hcoolccool_13, hcoolccool_1 <= hcoolccool_9, hcoolccool_1 <= hcoolccool_0, hcoolccool_1 <= hcoolccool_5)), And(hcoolc == hcoolccool_6, And(hcoolccool_6 <= hcoolccool_14, hcoolccool_6 <= hcoolccool_2, hcoolccool_6 <= hcoolccool_4, hcoolccool_6 <= hcoolccool_13, hcoolccool_6 <= hcoolccool_8, hcoolccool_6 <= hcoolccool_7, hcoolccool_6 <= hcoolccool_10, hcoolccool_6 <= hcoolccool_0, hcoolccool_6 <= hcoolccool_11, hcoolccool_6 <= hcoolccool_15, hcoolccool_6 <= hcoolccool_5, hcoolccool_6 <= hcoolccool_3, hcoolccool_6 <= hcoolccool_1, hcoolccool_6 <= hcoolccool_12, hcoolccool_6 <= hcoolccool_9)), And(hcoolc == hcoolccool_7, And(hcoolccool_7 <= hcoolccool_13, hcoolccool_7 <= hcoolccool_3, hcoolccool_7 <= hcoolccool_8, hcoolccool_7 <= hcoolccool_15, hcoolccool_7 <= hcoolccool_10, hcoolccool_7 <= hcoolccool_9, hcoolccool_7 <= hcoolccool_14, hcoolccool_7 <= hcoolccool_2, hcoolccool_7 <= hcoolccool_4, hcoolccool_7 <= hcoolccool_11, hcoolccool_7 <= hcoolccool_0, hcoolccool_7 <= hcoolccool_5, hcoolccool_7 <= hcoolccool_1, hcoolccool_7 <= hcoolccool_12, hcoolccool_7 <= hcoolccool_6)), And(hcoolc == hcoolccool_3, And(hcoolccool_3 <= hcoolccool_7, hcoolccool_3 <= hcoolccool_4, hcoolccool_3 <= hcoolccool_12, hcoolccool_3 <= hcoolccool_15, hcoolccool_3 <= hcoolccool_0, hcoolccool_3 <= hcoolccool_11, hcoolccool_3 <= hcoolccool_1, hcoolccool_3 <= hcoolccool_5, hcoolccool_3 <= hcoolccool_9, hcoolccool_3 <= hcoolccool_2, hcoolccool_3 <= hcoolccool_6, hcoolccool_3 <= hcoolccool_10, hcoolccool_3 <= hcoolccool_13, hcoolccool_3 <= hcoolccool_8, hcoolccool_3 <= hcoolccool_14)), And(hcoolc == hcoolccool_9, And(hcoolccool_9 <= hcoolccool_8, hcoolccool_9 <= hcoolccool_0, hcoolccool_9 <= hcoolccool_3, hcoolccool_9 <= hcoolccool_14, hcoolccool_9 <= hcoolccool_2, hcoolccool_9 <= hcoolccool_7, hcoolccool_9 <= hcoolccool_15, hcoolccool_9 <= hcoolccool_1, hcoolccool_9 <= hcoolccool_11, hcoolccool_9 <= hcoolccool_6, hcoolccool_9 <= hcoolccool_12, hcoolccool_9 <= hcoolccool_4, hcoolccool_9 <= hcoolccool_5, hcoolccool_9 <= hcoolccool_10, hcoolccool_9 <= hcoolccool_13)), And(hcoolc == hcoolccool_14, And(hcoolccool_14 <= hcoolccool_2, hcoolccool_14 <= hcoolccool_11, hcoolccool_14 <= hcoolccool_6, hcoolccool_14 <= hcoolccool_9, hcoolccool_14 <= hcoolccool_10, hcoolccool_14 <= hcoolccool_1, hcoolccool_14 <= hcoolccool_5, hcoolccool_14 <= hcoolccool_4, hcoolccool_14 <= hcoolccool_0, hcoolccool_14 <= hcoolccool_7, hcoolccool_14 <= hcoolccool_13, hcoolccool_14 <= hcoolccool_15, hcoolccool_14 <= hcoolccool_3, hcoolccool_14 <= hcoolccool_8, hcoolccool_14 <= hcoolccool_12)), And(hcoolc == hcoolccool_12, And(hcoolccool_12 <= hcoolccool_3, hcoolccool_12 <= hcoolccool_2, hcoolccool_12 <= hcoolccool_9, hcoolccool_12 <= hcoolccool_10, hcoolccool_12 <= hcoolccool_14, hcoolccool_12 <= hcoolccool_1, hcoolccool_12 <= hcoolccool_0, hcoolccool_12 <= hcoolccool_11, hcoolccool_12 <= hcoolccool_13, hcoolccool_12 <= hcoolccool_6, hcoolccool_12 <= hcoolccool_8, hcoolccool_12 <= hcoolccool_5, hcoolccool_12 <= hcoolccool_4, hcoolccool_12 <= hcoolccool_7, hcoolccool_12 <= hcoolccool_15))), hcool_1 == hcoolccool_1, hcool_14 == hcoolccool_14, hrestc == hrestcrest_0, hcool_7 == hcoolccool_7, hcool_12 == hcoolccool_12, hcool_9 == hcoolccool_9, hcool_3 == hcoolccool_3, hcool_13 == hcoolccool_13, hcool_8 == hcoolccool_8, hcool_15 == hcoolccool_15, hcool_0 == hcoolccool_0, hrest_0 == hrestcrest_0, hcool_10 == hcoolccool_10, hcool_6 == hcoolccool_6, hcool_5 == hcoolccool_5)
Sep = And(And(Or(hcoolccool_1 - hcoolccool_6 >= 0, hcoolccool_6 - hcoolccool_1 >= 0), Or(hcoolccool_1 - hcoolccool_11 >= 0, hcoolccool_11 - hcoolccool_1 >= 0), Or(hcoolccool_1 - hcoolccool_15 >= 0, hcoolccool_15 - hcoolccool_1 >= 0), Or(hcoolccool_1 - hcoolccool_9 >= 0, hcoolccool_9 - hcoolccool_1 >= 0), Or(hcoolccool_1 - hcoolccool_10 >= 0, hcoolccool_10 - hcoolccool_1 >= 0), Or(hcoolccool_1 - hcoolccool_2 >= 0, hcoolccool_2 - hcoolccool_1 >= 0), Or(hcoolccool_1 - hcoolccool_3 >= 0, hcoolccool_3 - hcoolccool_1 >= 0), Or(hcoolccool_1 - hcoolccool_8 >= 0, hcoolccool_8 - hcoolccool_1 >= 0), Or(hcoolccool_1 - hcoolccool_14 >= 0, hcoolccool_14 - hcoolccool_1 >= 0), Or(hcoolccool_1 - hcoolccool_12 >= 0, hcoolccool_12 - hcoolccool_1 >= 0), Or(hcoolccool_1 - hcoolccool_7 >= 0, hcoolccool_7 - hcoolccool_1 >= 0), Or(hcoolccool_1 - hcoolccool_5 >= 0, hcoolccool_5 - hcoolccool_1 >= 0), Or(hcoolccool_1 - hcoolccool_13 >= 0, hcoolccool_13 - hcoolccool_1 >= 0), Or(hcoolccool_1 - hcoolccool_4 >= 0, hcoolccool_4 - hcoolccool_1 >= 0), Or(hcoolccool_1 - hcoolccool_0 >= 0, hcoolccool_0 - hcoolccool_1 >= 0), Or(hcoolccool_6 - hcoolccool_11 >= 0, hcoolccool_11 - hcoolccool_6 >= 0), Or(hcoolccool_6 - hcoolccool_15 >= 0, hcoolccool_15 - hcoolccool_6 >= 0), Or(hcoolccool_6 - hcoolccool_9 >= 0, hcoolccool_9 - hcoolccool_6 >= 0), Or(hcoolccool_6 - hcoolccool_10 >= 0, hcoolccool_10 - hcoolccool_6 >= 0), Or(hcoolccool_6 - hcoolccool_2 >= 0, hcoolccool_2 - hcoolccool_6 >= 0), Or(hcoolccool_6 - hcoolccool_3 >= 0, hcoolccool_3 - hcoolccool_6 >= 0), Or(hcoolccool_6 - hcoolccool_8 >= 0, hcoolccool_8 - hcoolccool_6 >= 0), Or(hcoolccool_6 - hcoolccool_14 >= 0, hcoolccool_14 - hcoolccool_6 >= 0), Or(hcoolccool_6 - hcoolccool_12 >= 0, hcoolccool_12 - hcoolccool_6 >= 0), Or(hcoolccool_6 - hcoolccool_7 >= 0, hcoolccool_7 - hcoolccool_6 >= 0), Or(hcoolccool_6 - hcoolccool_5 >= 0, hcoolccool_5 - hcoolccool_6 >= 0), Or(hcoolccool_6 - hcoolccool_13 >= 0, hcoolccool_13 - hcoolccool_6 >= 0), Or(hcoolccool_6 - hcoolccool_4 >= 0, hcoolccool_4 - hcoolccool_6 >= 0), Or(hcoolccool_6 - hcoolccool_0 >= 0, hcoolccool_0 - hcoolccool_6 >= 0), Or(hcoolccool_11 - hcoolccool_15 >= 0, hcoolccool_15 - hcoolccool_11 >= 0), Or(hcoolccool_11 - hcoolccool_9 >= 0, hcoolccool_9 - hcoolccool_11 >= 0), Or(hcoolccool_11 - hcoolccool_10 >= 0, hcoolccool_10 - hcoolccool_11 >= 0), Or(hcoolccool_11 - hcoolccool_2 >= 0, hcoolccool_2 - hcoolccool_11 >= 0), Or(hcoolccool_11 - hcoolccool_3 >= 0, hcoolccool_3 - hcoolccool_11 >= 0), Or(hcoolccool_11 - hcoolccool_8 >= 0, hcoolccool_8 - hcoolccool_11 >= 0), Or(hcoolccool_11 - hcoolccool_14 >= 0, hcoolccool_14 - hcoolccool_11 >= 0), Or(hcoolccool_11 - hcoolccool_12 >= 0, hcoolccool_12 - hcoolccool_11 >= 0), Or(hcoolccool_11 - hcoolccool_7 >= 0, hcoolccool_7 - hcoolccool_11 >= 0), Or(hcoolccool_11 - hcoolccool_5 >= 0, hcoolccool_5 - hcoolccool_11 >= 0), Or(hcoolccool_11 - hcoolccool_13 >= 0, hcoolccool_13 - hcoolccool_11 >= 0), Or(hcoolccool_11 - hcoolccool_4 >= 0, hcoolccool_4 - hcoolccool_11 >= 0), Or(hcoolccool_11 - hcoolccool_0 >= 0, hcoolccool_0 - hcoolccool_11 >= 0), Or(hcoolccool_15 - hcoolccool_9 >= 0, hcoolccool_9 - hcoolccool_15 >= 0), Or(hcoolccool_15 - hcoolccool_10 >= 0, hcoolccool_10 - hcoolccool_15 >= 0), Or(hcoolccool_15 - hcoolccool_2 >= 0, hcoolccool_2 - hcoolccool_15 >= 0), Or(hcoolccool_15 - hcoolccool_3 >= 0, hcoolccool_3 - hcoolccool_15 >= 0), Or(hcoolccool_15 - hcoolccool_8 >= 0, hcoolccool_8 - hcoolccool_15 >= 0), Or(hcoolccool_15 - hcoolccool_14 >= 0, hcoolccool_14 - hcoolccool_15 >= 0), Or(hcoolccool_15 - hcoolccool_12 >= 0, hcoolccool_12 - hcoolccool_15 >= 0), Or(hcoolccool_15 - hcoolccool_7 >= 0, hcoolccool_7 - hcoolccool_15 >= 0), Or(hcoolccool_15 - hcoolccool_5 >= 0, hcoolccool_5 - hcoolccool_15 >= 0), Or(hcoolccool_15 - hcoolccool_13 >= 0, hcoolccool_13 - hcoolccool_15 >= 0), Or(hcoolccool_15 - hcoolccool_4 >= 0, hcoolccool_4 - hcoolccool_15 >= 0), Or(hcoolccool_15 - hcoolccool_0 >= 0, hcoolccool_0 - hcoolccool_15 >= 0), Or(hcoolccool_9 - hcoolccool_10 >= 0, hcoolccool_10 - hcoolccool_9 >= 0), Or(hcoolccool_9 - hcoolccool_2 >= 0, hcoolccool_2 - hcoolccool_9 >= 0), Or(hcoolccool_9 - hcoolccool_3 >= 0, hcoolccool_3 - hcoolccool_9 >= 0), Or(hcoolccool_9 - hcoolccool_8 >= 0, hcoolccool_8 - hcoolccool_9 >= 0), Or(hcoolccool_9 - hcoolccool_14 >= 0, hcoolccool_14 - hcoolccool_9 >= 0), Or(hcoolccool_9 - hcoolccool_12 >= 0, hcoolccool_12 - hcoolccool_9 >= 0), Or(hcoolccool_9 - hcoolccool_7 >= 0, hcoolccool_7 - hcoolccool_9 >= 0), Or(hcoolccool_9 - hcoolccool_5 >= 0, hcoolccool_5 - hcoolccool_9 >= 0), Or(hcoolccool_9 - hcoolccool_13 >= 0, hcoolccool_13 - hcoolccool_9 >= 0), Or(hcoolccool_9 - hcoolccool_4 >= 0, hcoolccool_4 - hcoolccool_9 >= 0), Or(hcoolccool_9 - hcoolccool_0 >= 0, hcoolccool_0 - hcoolccool_9 >= 0), Or(hcoolccool_10 - hcoolccool_2 >= 0, hcoolccool_2 - hcoolccool_10 >= 0), Or(hcoolccool_10 - hcoolccool_3 >= 0, hcoolccool_3 - hcoolccool_10 >= 0), Or(hcoolccool_10 - hcoolccool_8 >= 0, hcoolccool_8 - hcoolccool_10 >= 0), Or(hcoolccool_10 - hcoolccool_14 >= 0, hcoolccool_14 - hcoolccool_10 >= 0), Or(hcoolccool_10 - hcoolccool_12 >= 0, hcoolccool_12 - hcoolccool_10 >= 0), Or(hcoolccool_10 - hcoolccool_7 >= 0, hcoolccool_7 - hcoolccool_10 >= 0), Or(hcoolccool_10 - hcoolccool_5 >= 0, hcoolccool_5 - hcoolccool_10 >= 0), Or(hcoolccool_10 - hcoolccool_13 >= 0, hcoolccool_13 - hcoolccool_10 >= 0), Or(hcoolccool_10 - hcoolccool_4 >= 0, hcoolccool_4 - hcoolccool_10 >= 0), Or(hcoolccool_10 - hcoolccool_0 >= 0, hcoolccool_0 - hcoolccool_10 >= 0), Or(hcoolccool_2 - hcoolccool_3 >= 0, hcoolccool_3 - hcoolccool_2 >= 0), Or(hcoolccool_2 - hcoolccool_8 >= 0, hcoolccool_8 - hcoolccool_2 >= 0), Or(hcoolccool_2 - hcoolccool_14 >= 0, hcoolccool_14 - hcoolccool_2 >= 0), Or(hcoolccool_2 - hcoolccool_12 >= 0, hcoolccool_12 - hcoolccool_2 >= 0), Or(hcoolccool_2 - hcoolccool_7 >= 0, hcoolccool_7 - hcoolccool_2 >= 0), Or(hcoolccool_2 - hcoolccool_5 >= 0, hcoolccool_5 - hcoolccool_2 >= 0), Or(hcoolccool_2 - hcoolccool_13 >= 0, hcoolccool_13 - hcoolccool_2 >= 0), Or(hcoolccool_2 - hcoolccool_4 >= 0, hcoolccool_4 - hcoolccool_2 >= 0), Or(hcoolccool_2 - hcoolccool_0 >= 0, hcoolccool_0 - hcoolccool_2 >= 0), Or(hcoolccool_3 - hcoolccool_8 >= 0, hcoolccool_8 - hcoolccool_3 >= 0), Or(hcoolccool_3 - hcoolccool_14 >= 0, hcoolccool_14 - hcoolccool_3 >= 0), Or(hcoolccool_3 - hcoolccool_12 >= 0, hcoolccool_12 - hcoolccool_3 >= 0), Or(hcoolccool_3 - hcoolccool_7 >= 0, hcoolccool_7 - hcoolccool_3 >= 0), Or(hcoolccool_3 - hcoolccool_5 >= 0, hcoolccool_5 - hcoolccool_3 >= 0), Or(hcoolccool_3 - hcoolccool_13 >= 0, hcoolccool_13 - hcoolccool_3 >= 0), Or(hcoolccool_3 - hcoolccool_4 >= 0, hcoolccool_4 - hcoolccool_3 >= 0), Or(hcoolccool_3 - hcoolccool_0 >= 0, hcoolccool_0 - hcoolccool_3 >= 0), Or(hcoolccool_8 - hcoolccool_14 >= 0, hcoolccool_14 - hcoolccool_8 >= 0), Or(hcoolccool_8 - hcoolccool_12 >= 0, hcoolccool_12 - hcoolccool_8 >= 0), Or(hcoolccool_8 - hcoolccool_7 >= 0, hcoolccool_7 - hcoolccool_8 >= 0), Or(hcoolccool_8 - hcoolccool_5 >= 0, hcoolccool_5 - hcoolccool_8 >= 0), Or(hcoolccool_8 - hcoolccool_13 >= 0, hcoolccool_13 - hcoolccool_8 >= 0), Or(hcoolccool_8 - hcoolccool_4 >= 0, hcoolccool_4 - hcoolccool_8 >= 0), Or(hcoolccool_8 - hcoolccool_0 >= 0, hcoolccool_0 - hcoolccool_8 >= 0), Or(hcoolccool_14 - hcoolccool_12 >= 0, hcoolccool_12 - hcoolccool_14 >= 0), Or(hcoolccool_14 - hcoolccool_7 >= 0, hcoolccool_7 - hcoolccool_14 >= 0), Or(hcoolccool_14 - hcoolccool_5 >= 0, hcoolccool_5 - hcoolccool_14 >= 0), Or(hcoolccool_14 - hcoolccool_13 >= 0, hcoolccool_13 - hcoolccool_14 >= 0), Or(hcoolccool_14 - hcoolccool_4 >= 0, hcoolccool_4 - hcoolccool_14 >= 0), Or(hcoolccool_14 - hcoolccool_0 >= 0, hcoolccool_0 - hcoolccool_14 >= 0), Or(hcoolccool_12 - hcoolccool_7 >= 0, hcoolccool_7 - hcoolccool_12 >= 0), Or(hcoolccool_12 - hcoolccool_5 >= 0, hcoolccool_5 - hcoolccool_12 >= 0), Or(hcoolccool_12 - hcoolccool_13 >= 0, hcoolccool_13 - hcoolccool_12 >= 0), Or(hcoolccool_12 - hcoolccool_4 >= 0, hcoolccool_4 - hcoolccool_12 >= 0), Or(hcoolccool_12 - hcoolccool_0 >= 0, hcoolccool_0 - hcoolccool_12 >= 0), Or(hcoolccool_7 - hcoolccool_5 >= 0, hcoolccool_5 - hcoolccool_7 >= 0), Or(hcoolccool_7 - hcoolccool_13 >= 0, hcoolccool_13 - hcoolccool_7 >= 0), Or(hcoolccool_7 - hcoolccool_4 >= 0, hcoolccool_4 - hcoolccool_7 >= 0), Or(hcoolccool_7 - hcoolccool_0 >= 0, hcoolccool_0 - hcoolccool_7 >= 0), Or(hcoolccool_5 - hcoolccool_13 >= 0, hcoolccool_13 - hcoolccool_5 >= 0), Or(hcoolccool_5 - hcoolccool_4 >= 0, hcoolccool_4 - hcoolccool_5 >= 0), Or(hcoolccool_5 - hcoolccool_0 >= 0, hcoolccool_0 - hcoolccool_5 >= 0), Or(hcoolccool_13 - hcoolccool_4 >= 0, hcoolccool_4 - hcoolccool_13 >= 0), Or(hcoolccool_13 - hcoolccool_0 >= 0, hcoolccool_0 - hcoolccool_13 >= 0), Or(hcoolccool_4 - hcoolccool_0 >= 0, hcoolccool_0 - hcoolccool_4 >= 0)))
GihExt = And(ciRod_16hh, ciRod_9hh, ciRod_10hh, ciRod_4hh, ciRod_11hh, cicontrollerhh, ciRod_8hh, ciRod_5hh, ciRod_3hh, ciRod_15hh, ciRod_14hh, ciRod_0hh, ciRod_13hh, ciRod_6hh, ciRod_1hh, ciRod_7hh, ciRod_2hh, ciRod_12hh, EqsS, EqsC, Sep, AddInvs )
deadExt = And(GihExt, DisN)
print "Solving deadExt:" 
getCEX(deadExt)



safe = True
#Solving EF formula: 
EFformula = Exists([ct,p], And(Kp_all, ForAll([l0_16, l1_16, l0_9, l1_9, l0_10, l1_10, l0_4, l1_4, l0_11, l1_11, lc0, lc1, l0_8, l1_8, l0_5, l1_5, l0_3, l1_3, l0_15, l1_15, l0_14, l1_14, l0_0, l1_0, l0_13, l1_13, l0_6, l1_6, l0_1, l1_1, l0_7, l1_7, l0_2, l1_2, l0_12, l1_12, hcool_13, hrest_8, hrestc, x_12, hcool_6, hcool_1, hrest_13, hrest_12, hcool_5, x_2, x_13, hrest_1, hcool_9, hcool_0, x_8, hcoolc, hcool_15, hcool_10, hrest_16, x_6, x_1, xc, hrest_11, hcool_4, hrest_7, x_16, hcool_14, hrest_10, x_9, hrest_2, x_4, hrest_15, hcool_11, hcool_7, x_10, x_15, hrest_6, hcool_3, x_5, x_0, hrest_3, x_11, hcool_2, hcool_12, hrest_5, hrest_14, hcool_16, hrest_9, hcool_8, x_7, x_3, x_14, hrest_0, hrest_4, hcoolccool_13, hcoolccool_5, hcoolccool_8, hcoolccool_10, hcoolccool_11, hcoolccool_4, hcoolccool_12, hcoolccool_2, hcoolccool_3, hcoolccool_6, hcoolccool_0, hcoolccool_14, hcoolccool_9, hrestcrest_0, hcoolccool_15, hcoolccool_1, hcoolccool_7], Implies(Gih, And(safe, En)))))
s = Solver() 
s.add(EFformula) 
print s.check() 
print s.model()