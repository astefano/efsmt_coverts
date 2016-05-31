from z3 import *

p13 = Bool('p13')

beta1 = Int('beta1')

gamma1 = Int('gamma1')

t1 = Int('t1')

p11 = Bool('p11')

p12 = Bool('p12')

alpha1 = Int('alpha1')

p10 = Bool('p10')

eta1 = Int('eta1')

ts1 = Int('ts1')



Inv_philo1 = Or(And(p11,  gamma1 >= ts1,  ts1 >= 0,  ts1 == t1), And(p12,  3 >= t1,  gamma1 + t1 >= ts1,  ts1 >= t1,  t1 >= 0,  ts1 >= eta1 + t1), And(p13,  3 >= t1,  gamma1 >= 0,  gamma1 + t1 + 3 >= ts1,  gamma1 >= eta1,  ts1 >= 2 + t1,  t1 >= 0,  ts1 >= 2 + eta1 + t1), And(p10,  alpha1 >= t1,  gamma1 >= 0,  gamma1 + t1 + 3 >= ts1,  gamma1 >= eta1,  ts1 >= 2 + t1,  t1 >= 2,  ts1 >= 2 + eta1 + t1), And(p11,  alpha1 >= 2,  alpha1 + gamma1 + 3 >= beta1,  gamma1 >= ts1,  gamma1 >= eta1,  ts1 >= 0,  ts1 == t1), And(p12,  3 >= t1,  alpha1 >= 2,  alpha1 + gamma1 + 3 >= beta1,  gamma1 + t1 >= ts1,  ts1 >= t1,  t1 >= 0,  ts1 >= eta1 + t1), And(p13,  3 >= t1,  alpha1 >= 2,  alpha1 + gamma1 + 3 >= beta1,  gamma1 >= 0,  gamma1 + t1 + 3 >= ts1,  gamma1 >= eta1,  ts1 >= 2 + t1,  t1 >= 0,  ts1 >= 2 + eta1 + t1), And(p10,  alpha1 >= t1,  alpha1 + gamma1 + 3 >= beta1,  gamma1 >= 0,  gamma1 + t1 + 3 >= ts1,  gamma1 >= eta1,  ts1 >= 2 + t1,  t1 >= 2,  ts1 >= 2 + eta1 + t1))


f10 = Bool('f10')

f11 = Bool('f11')



Inv_fork1 = Or(f10, f11)


gamma2 = Int('gamma2')

p22 = Bool('p22')

p23 = Bool('p23')

p20 = Bool('p20')

alpha2 = Int('alpha2')

ts2 = Int('ts2')

p21 = Bool('p21')

eta2 = Int('eta2')

beta2 = Int('beta2')

t2 = Int('t2')



Inv_philo2 = Or(And(p21,  gamma2 >= ts2,  ts2 >= 0,  ts2 == t2), And(p22,  4 >= t2,  gamma2 + t2 >= ts2,  ts2 >= t2,  t2 >= 0,  ts2 >= eta2 + t2), And(p23,  2 >= t2,  gamma2 >= 0,  gamma2 + t2 + 4 >= ts2,  gamma2 >= eta2,  ts2 >= 3 + t2,  t2 >= 0,  ts2 >= 3 + eta2 + t2), And(p20,  alpha2 >= t2,  gamma2 >= 0,  gamma2 + t2 + 4 >= ts2,  gamma2 >= eta2,  ts2 >= 3 + t2,  t2 >= 1,  ts2 >= 3 + eta2 + t2), And(p21,  alpha2 >= 1,  alpha2 + gamma2 + 4 >= beta2,  gamma2 >= ts2,  gamma2 >= eta2,  ts2 >= 0,  ts2 == t2), And(p22,  4 >= t2,  alpha2 >= 1,  alpha2 + gamma2 + 4 >= beta2,  gamma2 + t2 >= ts2,  ts2 >= t2,  t2 >= 0,  ts2 >= eta2 + t2), And(p23,  2 >= t2,  alpha2 >= 1,  alpha2 + gamma2 + 4 >= beta2,  gamma2 >= 0,  gamma2 + t2 + 4 >= ts2,  gamma2 >= eta2,  ts2 >= 3 + t2,  t2 >= 0,  ts2 >= 3 + eta2 + t2), And(p20,  alpha2 >= t2,  alpha2 + gamma2 + 4 >= beta2,  gamma2 >= 0,  gamma2 + t2 + 4 >= ts2,  gamma2 >= eta2,  ts2 >= 3 + t2,  t2 >= 1,  ts2 >= 3 + eta2 + t2))


f20 = Bool('f20')
f21 = Bool('f21')



Inv_fork2 = Or(f20, f21)

safe =And(t1 + t2 <= 60)

s = Solver()
s.add(Exists([alpha1, beta1, gamma1, eta1, alpha2, beta2, gamma2, eta2], 
ForAll([t1, t2, ts1, ts2, p10, p11, p12, p13, p20, p21, p22, p23, f10, f11, f20, f21], 
And(alpha1>=10, beta1>=0, gamma1>=0, eta1>=0, alpha2>=0, beta2>=0, gamma2 >=0, eta2 >=0, Implies(And(Inv_philo1, Inv_philo2, Inv_fork1, Inv_fork2), safe))))
)

#s.add(Exists([alpha1, beta1, gamma1, eta1, alpha2, beta2, gamma2, eta2, p10, p11, p12, p13, p20, p21, p22, p23, f10, f11, f20, f21], And(Inv_philo1, Inv_philo2, Inv_fork1, Inv_fork2)))

#s.add(Exists([gamma1,ts1, t1], ForAll([p11], And(p11,  gamma1 >= ts1,  ts1 >= 0,  ts1 == t1))))

#s.add(Exists([gamma1], And(ts1 >= 10, ts1 <= 15, And(p11,  gamma1 >= ts1, ts1 == t1))))

print s.check()
print s.model()


def mkUppaalQuery(inv) : 
        #remove the starting "Or(" and the last ")"
        inv0 = inv[3:-1]
	invs = inv0.split("And")
	return "A[] (" + reduce(lambda a, b: a + b, map(lambda z: reduce(lambda x, y: x + " and " + y, z.split(",")),  invs)).replace(") and", ") or") + ")"

print mkUppaalQuery("Or(And(p11,  gamma1 >= ts1,  ts1 >= 0,  ts1 == t1), And(p12,  3 >= t1,  gamma1 + t1 >= ts1,  ts1 >= t1,  t1 >= 0,  ts1 >= eta1 + t1), And(p13,  3 >= t1,  gamma1 >= 0,  gamma1 + t1 + 3 >= ts1,  gamma1 >= eta1,  ts1 >= 2 + t1,  t1 >= 0,  ts1 >= 2 + eta1 + t1), And(p10,  alpha1 >= t1,  gamma1 >= 0,  gamma1 + t1 + 3 >= ts1,  gamma1 >= eta1,  ts1 >= 2 + t1,  t1 >= 2,  ts1 >= 2 + eta1 + t1), And(p11,  alpha1 >= 2,  alpha1 + gamma1 + 3 >= beta1,  gamma1 >= ts1,  gamma1 >= eta1,  ts1 >= 0,  ts1 == t1), And(p12,  3 >= t1,  alpha1 >= 2,  alpha1 + gamma1 + 3 >= beta1,  gamma1 + t1 >= ts1,  ts1 >= t1,  t1 >= 0,  ts1 >= eta1 + t1), And(p13,  3 >= t1,  alpha1 >= 2,  alpha1 + gamma1 + 3 >= beta1,  gamma1 >= 0,  gamma1 + t1 + 3 >= ts1,  gamma1 >= eta1,  ts1 >= 2 + t1,  t1 >= 0,  ts1 >= 2 + eta1 + t1), And(p10,  alpha1 >= t1,  alpha1 + gamma1 + 3 >= beta1,  gamma1 >= 0,  gamma1 + t1 + 3 >= ts1,  gamma1 >= eta1,  ts1 >= 2 + t1,  t1 >= 2,  ts1 >= 2 + eta1 + t1))".replace("p1", "P1.p1")
)


A[] (
(P1.p11 and gamma1 >= ts1 and   ts1 >= 0 and   ts1 == t1) or  
(P1.p12 and 3 >= t1 and   gamma1 + t1 >= ts1 and   ts1 >= t1 and   t1 >= 0 and   ts1 >= eta1 + t1) or  
(P1.p13 and 3 >= t1 and   gamma1 >= 0 and   gamma1 + t1 + 3 >= ts1 and   gamma1 >= eta1 and   ts1 >= 2 + t1 and   t1 >= 0 and   ts1 >= 2 + eta1 + t1) or  
(P1.p10 and alpha1 >= t1 and   gamma1 >= 0 and   gamma1 + t1 + 3 >= ts1 and   gamma1 >= eta1 and   ts1 >= 2 + t1 and   t1 >= 2 and   ts1 >= 2 + eta1 + t1) or  
(P1.p11 and alpha1 >= 2 and   alpha1 + gamma1 + 3 >= beta1 and   gamma1 >= ts1 and   gamma1 >= eta1 and   ts1 >= 0 and   ts1 == t1) or  
(P1.p12 and 3 >= t1 and   alpha1 >= 2 and   alpha1 + gamma1 + 3 >= beta1 and   gamma1 + t1 >= ts1 and   ts1 >= t1 and   t1 >= 0 and   ts1 >= eta1 + t1) or  
(P1.p13 and 3 >= t1 and   alpha1 >= 2 and   alpha1 + gamma1 + 3 >= beta1 and   gamma1 >= 0 and   gamma1 + t1 + 3 >= ts1 and   gamma1 >= eta1 and   ts1 >= 2 + t1 and   t1 >= 0 and   ts1 >= 2 + eta1 + t1) or
(P1.p10 and   alpha1 >= t1 and   alpha1 + gamma1 + 3 >= beta1 and   gamma1 >= 0 and   gamma1 + t1 + 3 >= ts1 and   gamma1 >= eta1 and   ts1 >= 2 + t1 and   t1 >= 2 and   ts1 >= 2 + eta1 + t1))


