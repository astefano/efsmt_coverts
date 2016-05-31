from z3 import *

def printModels(models):
	for m in models:
		printModel(m)

def printModel(M):
	print "["
	for d in M: 
		if M[d].sexpr() != 'False':
			print "%s = %s" % (d.name(), M[d])
	print "]"

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
r, y = Ints('r y')
q, x = Ints('q x')

ciC2 = And(Implies(c20, And(5 >= y,  y >= 0)), Implies(c21, And(3 >= y,  y >= 0,  5 >= r)), Implies(c20, And(5 >= y,  y >= 0,  5 >= r)), Not(And(c20, c21)))

ciC1 = And(Implies(c10, And(7 >= x,  x >= 0)), Implies(c11, And(10 >= x,  x >= 0,  x >= q,  7 >= q)), Implies(c10,  And(7 >= x,  x >= 0,  7 >= q)), Not(And(c10, c11)))

#abstract reach
absReachII = Or(And(c20, c10), And(c20, c11), And(c21, c10), And(c21, c11)) 

#Enabled guided by absReach
En = Or(And(c20, c10, -r + y >= 0, -y >= -5, -x >= -7), And(c20,c11, -r + y >= 0, -y >= -5, -x >= -10), And(c21,c10, -q + x >= 0, -y >= -3, -x >= -7), And(c21, c11, -y >= -3, -x >= -10), And(c20,c10, -q + x >= 0, -y >= -5, -x >= -7))

PosClks = And(r >= 0, q >= 0)
Gi = And(ciC2, ciC1, absReachII)

bad = And(Gi, x < y)
print "Solving bad:" 
getCEX(bad)

safe = Implies(c11, x < y)
#Solving EF formula: 
EFformula = Exists([r,q], And(r <= 5, q <= 7, PosClks, ForAll([c20, c21, c10, c11, y, x], Implies(And(x >= 0, y >= 0, Gi), And(safe, En)))))
#EFformula = Exists([r,q], ForAll([c20, c21, c10, c11, y, x],  And(PosClks, Implies(Gi, And(safe)))))
#EFformula = Exists([r,q], And(PosClks, Implies(Gi, And(safe))))
#EFformula = Exists([q], ForAll(x, Implies(x >= q, x >= 4)))
#EFformula = Exists([q], Implies(x >= q, x >= 4))
s = Solver() 
s.add(EFformula) 
print s.check() 
print s.model()