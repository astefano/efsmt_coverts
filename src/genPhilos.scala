package org

import parma_polyhedra_library._

//object GenPhilos extends ZoneGraphVV with genEF {
object GenPhilos extends ZoneGraphVV {

  def mkPhiloTimed(i: Int, cp2: Int, ce: Int, cp3: Int, cr: Int) = {
    val p0: Location = "p" + i + "0"
    val p1: Location = "p" + i + "1"
    val p2: Location = "p" + i + "2"
    val p3: Location = "p" + i + "3"
    val locs = Set(p0, p1, p2, p3)
    val ts = new Variable(0)    
    val le_ts = new Linear_Expression_Variable(ts)
    val t = new Variable(1)    
    val le_t = new Linear_Expression_Variable(t)
    val gamma = new Variable(2)    
    val le_gamma = new Linear_Expression_Variable(gamma)
    val alpha = new Variable(3)    
    val le_alpha = new Linear_Expression_Variable(alpha)
    val beta = new Variable(4)    
    val le_beta = new Linear_Expression_Variable(beta)
    val eta = new Variable(5)    
    val le_eta = new Linear_Expression_Variable(eta)
    val clks = Map(ts -> ("ts"+i), t -> ("t"+i), gamma -> ("gamma"+i), alpha -> ("alpha"+i), beta -> ("beta"+i), eta -> ("eta"+i))    
    val dim = clks.size
    //constant in the inv of p2
    val coeff_cp2 = new Coefficient(cp2)
    val le_cp2 = new Linear_Expression_Coefficient(coeff_cp2)    
    //constant in the guard of eat
    val coeff_ce = new Coefficient(ce)
    val le_ce = new Linear_Expression_Coefficient(coeff_ce)
    //constant in the inv of p3
    val coeff_cp3 = new Coefficient(cp3)
    val le_cp3 = new Linear_Expression_Coefficient(coeff_cp3)    
    //constant in the guard of release
    val coeff_cr = new Coefficient(cr)
    val le_cr = new Linear_Expression_Coefficient(coeff_cr)

    val invp0 = new NNC_Polyhedron(dim, Degenerate_Element.UNIVERSE)
    invp0.add_constraint(new Constraint(le_ts, Relation_Symbol.LESS_OR_EQUAL, le_alpha))
    val invp1 = new NNC_Polyhedron(dim, Degenerate_Element.UNIVERSE)
    invp1.add_constraint(new Constraint(le_t, Relation_Symbol.LESS_OR_EQUAL, le_gamma))
    val invp2 = new NNC_Polyhedron(dim, Degenerate_Element.UNIVERSE)
    invp2.add_constraint(new Constraint(le_t, Relation_Symbol.LESS_OR_EQUAL, le_cp2))
    val invp3 = new NNC_Polyhedron(dim, Degenerate_Element.UNIVERSE)
    invp3.add_constraint(new Constraint(le_t, Relation_Symbol.LESS_OR_EQUAL, le_cp3))

    val invM: InvMap = Map((p0 -> new NNC_Polyhedron(invp0)), 
			   (p1 -> new NNC_Polyhedron(invp1)), 
			   (p2 -> new NNC_Polyhedron(invp2)),
			   (p3 -> new NNC_Polyhedron(invp3))
			 )

    val gtake = new NNC_Polyhedron(dim, Degenerate_Element.UNIVERSE)
    gtake.add_constraint(new Constraint(le_t, Relation_Symbol.GREATER_OR_EQUAL, le_eta))
    val geat = new NNC_Polyhedron(dim, Degenerate_Element.UNIVERSE)
    geat.add_constraint(new Constraint(le_t, Relation_Symbol.GREATER_OR_EQUAL, le_ce))
    val grel = new NNC_Polyhedron(dim, Degenerate_Element.UNIVERSE)
    grel.add_constraint(new Constraint(le_t, Relation_Symbol.GREATER_OR_EQUAL, le_cr))
    val gend = new NNC_Polyhedron(dim, Degenerate_Element.UNIVERSE)
    gend.add_constraint(new Constraint(le_ts, Relation_Symbol.GREATER_OR_EQUAL, le_beta))
    val rtake: Reset = Set((t, 0))
    val reat: Reset = Set((t, 0))
    val rrel: Reset = Set()
    val rend: Reset = Set((t, 0),(ts, 0))
    val t1: Transition = mkTrans(source=p0, p="endphio"+i, g=new NNC_Polyhedron(gend), r=rend, sink=p1)
    val t2: Transition = mkTrans(source=p1, p="takeleftphio"+i, g=new NNC_Polyhedron(gtake), r=rtake, sink=p2)
    val t3: Transition = mkTrans(source=p2, p="eatphio"+i, g=new NNC_Polyhedron(geat), r=reat, sink=p3)
    val t4: Transition = mkTrans(source=p3, p="releasephio"+i, g=new NNC_Polyhedron(grel), r=rrel, sink=p0)
    val trans = Set(t1, t2, t3, t4)	
    val params : Params = Set(("gamma"+i),("alpha"+i),("beta"+i),("eta"+i))
    val philo = (("Phio"+i), p1, locs, trans, clks, invM, emptyVV, params)
    philo	
  }

  def mkPhiloUntimed(i: Int) = {
    val p0: Location = "p" + i + "0"
    val p1: Location = "p" + i + "1"
    val p2: Location = "p" + i + "2"
    val p3: Location = "p" + i + "3"
    val locs = Set(p0, p1, p2, p3)
    val clks : ClkMap = Map()
    val dim = clks.size

    //true invariants have univ polygones
    val trueInv = new NNC_Polyhedron(dim, Degenerate_Element.UNIVERSE)
    val invM: InvMap = Map((p0 -> new NNC_Polyhedron(trueInv)), 
			   (p1 -> new NNC_Polyhedron(trueInv)), 
			   (p2 -> new NNC_Polyhedron(trueInv)),
			   (p3 -> new NNC_Polyhedron(trueInv))
			 )

    val trueGuard = new NNC_Polyhedron(dim, Degenerate_Element.UNIVERSE)
    val r1: Reset = Set()
    val r2: Reset = Set()
    val r3: Reset = Set()
    val r4: Reset = Set()
    val t1: Transition = mkTrans(source=p0, p="endphio"+i, g=new NNC_Polyhedron(trueGuard), r=r1, sink=p1)
    val t2: Transition = mkTrans(source=p1, p="takeleftphio"+i, g=new NNC_Polyhedron(trueGuard), r=r2, sink=p2)
    val t3: Transition = mkTrans(source=p2, p="eatphio"+i, g=new NNC_Polyhedron(trueGuard), r=r3, sink=p3)
    val t4: Transition = mkTrans(source=p3, p="releasephio"+i, g=new NNC_Polyhedron(trueGuard), r=r4, sink=p0)
    val trans = Set(t1, t2, t3, t4)	
    val philo = (("Phio"+i), p1, locs, trans, clks, invM, emptyVV)
    philo	
  }

  def mkFork(i: Int) = {
    val f0: Location = "f" + i + "0"
    val f1: Location = "f" + i + "1"
    val locs = Set(f0, f1)
    val clks :ClkMap = Map()
    val dim = clks.size

    //true invariants have univ polygones
    val trueInv = new NNC_Polyhedron(dim, Degenerate_Element.UNIVERSE)
    val invM: InvMap = Map((f0 -> new NNC_Polyhedron(trueInv)), 
			   (f1 -> new NNC_Polyhedron(trueInv))
			 )

    val trueGuard = new NNC_Polyhedron(dim, Degenerate_Element.UNIVERSE)
    val r1: Reset = Set()
    val r2: Reset = Set()
    val t1: Transition = mkTrans(source=f0, p="takefork"+i, g=new NNC_Polyhedron(trueGuard), r=r1, sink=f1)
    val t2: Transition = mkTrans(source=f1, p="releasefork"+i, g=new NNC_Polyhedron(trueGuard), r=r2, sink=f0)
    val trans = Set(t1, t2)	
    val fork = (("Fork"+i), f0, locs, trans, clks, invM, emptyVV)
    fork	
  }

/*
  //p0 == !pl && !pr
  def p0(i: int) = mand(List("!" + "p"+i+"l", "!" + "p"+i+"r"))

  //p1 ==  pl && !pr
  def p1(i: int) = mand(List(      "p"+i+"l", "!" + "p"+i+"r"))

  //p2 == !pl &&  pr
  def p2(i: int) = mand(List("!" + "p"+i+"l",       "p"+i+"r"))

  //p3 ==  pl &&  pr
  def p3(i: int) = mand(List(      "p"+i+"l",       "p"+i+"r"))

  //fi0 == !fi
  def f0(i: int) = "!f"+i

  //fi1 == fi
  def f1(i: int) = "f"+i

  def appi(s: String, i: int) = s + i

  // at p11 /\ f10 (f10 is !f1)
  // en(take1) = ((p11 && !f1) -> ([t1 <= gamma1]))
  def enTake(i: int) = mand(List(p1(i), f0(i), mkIneq(appi("t", i) + " <= " + appi("gamma", i))))

  //at p12 /\ f20 
  //en(eat1) = ((p12 && !f2) -> ([t1 <= 3])) 
  def enEat(i: int, n: int) = {
    var i1 = i
    if (i1 + 1 == n)
        i1 = 0
     mand(List(p2(i), f0(i1+1), mkIneq(appi("t", i) + " <= 3")))
  }

# p13 /\ f11 /\ f21
# en(release1) = ((p13 && f1 && f2) -> ([2 - alpha1 <= t1 - ts1] && [t1 - ts1 <= 3] && [ts1 <= alpha1] && [t1 <= 3])) 
def enRelease(i, n):
    i1 = i
    if i1 + 1 == n:
        i1 = 0
     mand([p3(i), f1(i), f1(i1+1), 
                 mkIneq(appi("2 - alpha", i) + " <= " + appi("t", i) + " - " + appi("ts", i)), 
                 mkIneq("3 >= " + appi("t", i) + " - " + appi("ts", i)), 
                 mkIneq(appi("ts", i) + " <= " + appi("alpha", i)),
                 mkIneq(appi("t", i) + " <= 3")
             ])

# en(reset) = ((p10 && p20 -> ([ts1 <= alpha1] && [ts2 <= alpha2] && [ts2 - ts1 <= alpha2 - beta1] && [ts1 - ts2 <= alpha1 - beta2]))
def enReset(n):
    l = [p0(i) for i in range(1,n+1)]
    for i in range(1,n+1):
        l.append(mkIneq(appi("ts", i) + " <= " + appi("alpha", i)))
        for j in range(1,n+1):
            if (i != j):
                l.append(mkIneq(appi("t", i) + " - " + appi("ts", j) + " <= " + appi("alpha", i) +  " - " + appi("beta", j)))
     mand(l)


def guaranteePhilo(n):
    l = []
    for i in range(1, n+1):
        l.append(enTake(i))
        l.append(enEat(i, n+1))
        l.append(enRelease(i, n+1))
    l.append(enReset(n))
     "Guarantee( " + mor(l) + " )"
*/

  def next(i: Int, n: Int) = if ((i + 1) > n) 1 else i + 1

  /*
   * take_i : {takeleftphioi, takeforki}
   * eat_i: {eatphioi, takeforki+1}
   * release_i: {releasephioi, releaseforki, releaseforki+1}
   * reset: {endphioi, \forall i}
   */ 

  def takeIA(i: Int) = List("takeleftphio"+i, "takefork"+i)
  def eatIA(i: Int, n: Int) = List("eatphio"+i, "takefork"+next(i, n))
  def releaseIA(i: Int, n: Int) = List("releasephio"+i, "releasefork"+i, "releasefork"+next(i, n))
  def resetIA(n: Int) = (for(i <- (1 to n)) yield "endphio"+i).toList
	       
  def genIM(n: Int) = (1 to n).flatMap{i => List(takeIA(i), eatIA(i, n), releaseIA(i, n))}:+resetIA(n)// :+List(eps)

  def main(args: Array[String]) {

    val nphilos = args(0).toInt
    val nforks = nphilos

    var philosEFIn = ""

    val c1 = List(3, 6, 5, 8, 7) 
    val c2 = List(2, 3, 1, 5, 2)
    val c3 = List(3, 4, 7, 3, 6)
    val c4 = List(2, 1, 3, 1, 5)

    (1 to nphilos) foreach {
      i =>
	philosEFIn += "\n%% constants used at p" + (i-1) + "2, on eat" + (i-1) + ", at p" + (i-1) + "3 and on release" + (i-1) + ": " + c1(i-1) + " " + c2(i-1) + " " + c3(i-1) + " " +c4(i-1) + "\n"    
    }

    val modelPath = wd + "Imitator/Philos/"
    try {
      val dir = new java.io.File(modelPath)    
      val outs = dir.listFiles.filter(f => !f.isDirectory).map(f => f.toString).filter(fs => fs.endsWith(".imi")).toList.map{x => (x, runImitator(x))} 
      outs foreach {
	outi =>
	  val file = outi._1
	  val out = outi._2
	  philosEFIn += "\n" + imiDecl2EFDecl(file) + "\n\n" + states2CIEF(out)
	  //println(loadImi(file))
      }
    }  

    Parma_Polyhedra_Library.initialize_library()   

    val im = genIM(nphilos)
    val ims = im.map{_.toSet}.toSet
/*
    val imWithEps = ims
    val imf = imWithEps.map{_.toList}.toList
    println("imf = " + imf)
    val eqs = getEqsSimpl(imf, false)    
    println("eqs = " + eqs)

    //philosEFIn += "\n\n" + "Assumption(" + eqs + ")\n\n\n"
    
    val systemUntimed = ((1 to nphilos).map{mkPhiloUntimed(_)} ++ (1 to nforks).map{mkFork(_)}).toList
    val ii = genII(systemUntimed, ims)
    //println("ii = " + ii)
    //philosEFIn += "%" + ii + "\n"

    //println(genDISInteraction(takeIA(1), systemTimed))
    //println(genDISInteraction(eatIA(1, nphilos), systemTimed))
    //println(genDISIAG(releaseIA(1, nphilos), systemTimed, List(("p13",0),("p22",1),("p31",2),("f11",3), ("f21",4))))
    //println(genDISInteraction(resetIA(nphilos), systemTimed))
*/

    val philos = (1 to nphilos).map{i => mkPhiloTimed(i, c1(i-1), c2(i-1), c3(i-1), c4(i-1))}
    val systemTimed = (philos.map{philo => getTA(philo)} ++ (1 to nforks).map{mkFork(_)}).toList

    philosEFIn += genAbsReach_En(systemTimed, ims)

    //println(genDIS(im.toList, systemTimed))

    philos foreach {
      ta => 
	mkImi(ta)
    }

    val ta = loadImi(wd + "Imitator/Philos/philo1.imi")
    println(toString(ta))

    import java.util.Calendar
    import java.text.SimpleDateFormat

    val today = Calendar.getInstance.getTime
    val curTimeFormat = new SimpleDateFormat("D_M_Y")

    val date = curTimeFormat.format(today)

    write2File("philosEF" + nphilos + "-" + date, philosEFIn)

    Parma_Polyhedra_Library.finalize_library()

  }
}


