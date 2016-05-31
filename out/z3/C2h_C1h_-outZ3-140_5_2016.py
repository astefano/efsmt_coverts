from z3 import *

def getCEX(F):
    toSolve = Solver()
    toSolve.add(F)
    if toSolve.check() == sat:
        m = toSolve.model()
        printModel(m)
    else:
        print "no solution"

def printModels(models):
	for m in models:
		printModel(m)

def printModel(M):
	print "["
	for d in M: 
		if M[d].sexpr() != 'False':
			print "%s = %s" % (d.name(), M[d])
	print "]"


c20, c21 = Bools('c20 c21')
s20, s21, s22 = Bools('s20 s21 s22')

c10, c11 = Bools('c10 c11')
s10, s11, s12 = Bools('s10 s11 s12')

r, ha2, hc, y = Ints('r ha2 hc y')
hb, q, x, ha1 = Ints('hb q x ha1')

#ciC2hh = And(Implies(c20, Or(And(5 >= y,  y >= 0,  y == hc,  y == ha2), And(5 >= y,  hc >= y,  y >= 0,  y + 3 >= hc,  5 >= r,  y == ha2))), Implies(c21, And(3 >= y,  y >= 0,  y + 5 >= ha2,  ha2 >= y,  ha2 >= r + y,  y == hc)), Not(And(c20, c21)))

ciC2hh = And(
Implies(s20, And(c20, 5 >= y,  y >= 0,  y == hc,  y == ha2)), 
Implies(s21, And(c20, 5 >= y,  hc >= y,  y >= 0,  y + 3 >= hc,  5 >= r,  y == ha2)), 
Implies(s22, And(c21, 3 >= y,  y >= 0,  y + 5 >= ha2,  ha2 >= y,  ha2 >= r + y,  y == hc)), 
Implies(c20, Or(s20, s21)),
Implies(c21, s22),
Not(And(s20, s21)), Not(And(s20, s22)), Not(And(s21, s22)),
Not(And(c20, c21))
)

#ciC2hh = And(Or(And(c20,  5 >= y,  y >= 0,  y == hc,  y == ha2), And(c21,  3 >= y,  y >= 0,  y + 5 >= ha2,  ha2 >= y,  ha2 >= r + y,  y == hc), And(c20,  5 >= y,  hc >= y,  y >= 0,  y + 3 >= hc,  5 >= r,  y == ha2)), Not(And(c20, c21)))

#ciC1hh = And(Implies(c10,  Or(And(7 >= x,  x >= 0,  x == hb,  x == ha1), And(7 >= x,  hb >= x,  x >= 0,  x + 10 >= hb,  7 >= q,  x + 10 >= q + hb,  x == ha1))), Implies(c11,  And(10 >= x,  x >= hb,  hb >= 0,  hb + 7 >= x,  x >= q + hb,  x == ha1)), Not(And(c10, c11)))

ciC1hh = And(
Implies(s10, And(c10, 7 >= x,  x >= 0,  x == hb,  x == ha1)), 
Implies(s11, And(c10, 7 >= x,  hb >= x,  x >= 0,  x + 10 >= hb,  7 >= q,  x + 10 >= q + hb,  x == ha1)), 
Implies(s12, And(c11, 10 >= x,  x >= hb,  hb >= 0,  hb + 7 >= x,  x >= q + hb,  x == ha1)), 
Implies(c10, Or(s10, s11)),
Implies(c11, s12),
Not(And(s10, s11)), Not(And(s10, s12)), Not(And(s11, s12)),
Not(And(c10, c11))
)

#ciC1hh = And(Or(And(c10,  7 >= x,  x >= 0,  x == hb,  x == ha1), And(c11,  10 >= x,  x >= hb,  hb >= 0,  hb + 7 >= x,  x >= q + hb,  x == ha1), And(c10,  7 >= x,  hb >= x,  x >= 0,  x + 10 >= hb,  7 >= q,  x + 10 >= q + hb,  x == ha1)), Not(And(c10, c11)))

#abstract reach
absReachII = Or(And(c20, c10), And(c20, c11), And(c21, c10), And(c21, c11), And(c20, c10)) 
#absReachII = And(c20, c10)

#Enabled guided by absReach
En = Or(And(c20,c10, -r + y >= 0, -y >= -5, -x >= -7), And(c20,c11, -r + y >= 0, -y >= -5, -x >= -10), And(c21,c10, -q + x >= 0, -y >= -3, -x >= -7), And(c21, c11, -y >= -3, -x >= -10), And(c20,c10, -q + x >= 0, -y >= -5, -x >= -7))

ha1a2, hb, hc = Ints('ha1a2 hb hc')
EqsS = ha1 == ha2

EqsC = And(ha1 == ha1a2, ha2 == ha1a2, hb == hb, hc == hc)
Sep = True

Params = And(r >= 0, q >= 0)
PosClks = And(ha2 >= 0, hc >= 0, y >= 0, hb >= 0, q >= 0, x >= 0, ha1 >= 0, hb >= 0, hc >= 0) #, ha1a2 >= 0
Gih = And(ciC2hh, ciC1hh, absReachII, EqsS)#, EqsC, Sep)

bad = And(Gih, x < y)
print "Solving bad:" 
getCEX(bad)

bad2 = And(Gih, 11 < x)
print "Solving bad2:" 
getCEX(bad2)

Gi = And(ciC2hh, ciC1hh, absReachII)

safe = Implies(c11, x >= 11)
#Solving EF formula: 
EFformula = Exists([r, q], And(r <= 5, q <= 7, Params, ForAll([c20, c21, c10, c11, y, x, hb, hc, ha1, ha2, s10, s11, s12, s20, s21, s22], Implies(And(PosClks, Gih), And(En, safe)))))
s = Solver() 
s.add(EFformula) 
print s.check() 
print s.model()

#print simplify(substitute(Gih, (r, IntVal(1)), (q, IntVal(8))))
#print simplify(substitute(En, (r, IntVal(1)), (q, IntVal(8))))