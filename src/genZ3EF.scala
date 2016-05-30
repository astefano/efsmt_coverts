package org

import scalax.io._
import scalax.file.{ FileOps, Path, NotFileException }
import java.io.FileNotFoundException
import scala.util.control.Exception._

import scala.sys.process._

import scala.sys

trait genZ3EF {

  //var IMITATORPATH = "/home/lastefan/Documents/tools/imitator/./IMITATOR64 "

  //var EFSMTPATH = "/home/lastefan/Documents/verimag/timed-orch-bip/cav15/efsmt/./test "
  
  var DEP = "dependencies/"

  var IMITATORPATH = DEP + "./IMITATOR64 "

  var HYMITATORPATH = DEP + "./HYMITATOR "

  var EFSMTPATH = DEP + "./test "


  def runImitator(filePath: String) = { 
    //val cmd = ("/local/astefano/tools/imitator/./IMITATOR64 " + filePath + " -mode reachability -with-dot -with-log") 
      
    val cmd = (IMITATORPATH + filePath + " -mode reachability -with-dot -with-log") 

    val out = new StringBuilder
    val err = new StringBuilder

    val logger = ProcessLogger(
      (o: String) => out.append(o),
      (e: String) => err.append(e))
    
    cmd ! logger
    //println("runImitator: cmd = " + cmd + "\n\n", 2)

    val all = out.toString + err.toString 
    //println(all)
    if (err.toString != "") {
      println("imitator returned err: " + err.toString)
      err.toString
    }
    else 
      filePath.replace("imi","states")
  }

  def runHymitator(filePath: String) = {       
    val cmd = (HYMITATORPATH + filePath + " -mode reachability -fancy") 

    val out = new StringBuilder
    val err = new StringBuilder

    val logger = ProcessLogger(
      (o: String) => out.append(o),
      (e: String) => err.append(e))
    
    cmd ! logger
    //println("runHymitator: cmd = " + cmd + "\n\n", 2)

    val all = out.toString + err.toString 
    println(all)
    if (err.toString != "") {
      println("hymitator returned err: " + err.toString)
      err.toString
    }
  }

  def genA(s: String, typeV: String = "") = "Forall(" + s + ")" + " " + typeV

  def genE(s: String, typeV: String = "") = "Exists(" + s + ")" + " " + typeV

  def mkIneq(s: String) = "[" + s + "]"

  def mand(l: List[String]) = l.foldLeft("")((r,c) => r + " && " + c)

  def mor(l: List[String]) = l.foldLeft("")((r,c) => r + " || " + c)

  /** transforms the content from statesFile into a formula for EFSMT
    * @param statesFile is the file name f.states file resulted from calling imitator on f.imi
    * 
    */ 
  def states2CIEF(statesFile: String) = {
    val file = Path.fromString(statesFile)
    val lines = file.lines()
    //the resulting component invariant
    var ci = ""
    lines foreach {
      l =>
	val lt = l.trim()
	if (!lt.startsWith("/") && 
	    !lt.startsWith("*") && 
	    !lt.startsWith("DESCRIPTION") && 
	    !lt.startsWith("STATE") && 
	    !lt.contains(" via ") &&
	    !lt.equals("\n")) {
	      //line of form: <TA_NAME>:<LOC_NAME> ==>
	      if (lt.contains(":") && lt.contains("==>")) {		
		val loc = lt.split(":")(1).split("==>")(0) 
		ci += " || " + loc
	      }
	      if (lt.startsWith("&")) {
		//line of form: & term1 op term2 where op \in {>=, =}
		val ct = lt.drop(1).replace(" = ", " == ")
		if (ct.trim != "true")
		  ci += " && " + mkIneq(ct)
	      }	    
	    }
    }
    //drop the first 4 chars (" || ")
    "Assumption(" + ci.drop(4) + ")"
  }

   def imiDecl2EFDecl(imiFile: String) = {
     val file = Path.fromString(imiFile)
     val lines = file.lines()
     //a set of Forall, Exists declarations
     var declS = Set[String]()
     //the set of params
     var paramSet = Set[String]()
     lines foreach {
       l =>
	 val lt = l.trim()
	 //line is of form: loc <loc_name>:
	 if (lt.startsWith("loc "))	 
	   declS += genA(lt.drop(4).split(":")(0).trim)
	 else if (lt.contains(":"))
	   if (lt.contains("parameter")) {
	     val params = lt.split("parameter")(0).split(":")(0).split(",")
	     paramSet ++= params.map(_.trim).toSet
	     params.map(x => genE(x.trim, "INT")) foreach {
	       el =>
		 declS += el
	     }
	   }
	   if (lt.contains("clock")) {
	     val clks = lt.split("clock")(0).split(":")(0).split(",")
	     //declarations and assumption about clocks >= 0
	     clks.map(x => genA(x.trim, "REAL")) foreach {
	       el =>
		 declS += el
	     }	      
	     declS += clks.foldLeft("")((r, c) => r + "\n" + mkEFAssumptionClk(c.trim, "0")) + "\n"
	   }
     }
     (declS.foldLeft("")((r,c) => r + "\n" + c) + "\n", paramSet)
   }

  def mkEFAssumption(s: String) = "Assumption(" + s + ")"

  def mkEFAssumptionClk(l: String, r: String, op: String=">=") = "Assumption(" + mkIneq(l + " " + op + " " + r) + ")"

  def mkEFCond(l: String, r: String, op: String=">") = "Condition(" + mkIneq(l + " " + op + " " + r) + ")"

  def mkEFCondFromParams(params: Map[String, String], op: String = ">=") = {
    "\n" + params.foldLeft("")((r,c) => r + "\n" + mkEFCond(c._1, c._2,op)) + "\n"
  }

  def runEF(efFile: String) = {
    val cmd = (EFSMTPATH + " " + efFile)

    val out = new StringBuilder
    val err = new StringBuilder

    val logger = ProcessLogger(
      (o: String) => out.append(o),
      (e: String) => err.append(e))
    
    cmd ! logger
    println("runEFSMT: cmd = " + cmd + "\n\n", 2)

    println("err=" + err.toString)

    val outStr = out.toString

    println("out=" + outStr)

    val isSat = outStr.contains("satisfying assignment")
    
    if (!isSat) {
      println("[runEF]: unsat!")
      Map[String, String]()
    }
    else {
      val paramvals = outStr.split("satisfying assignment ===")(1).split(":") map {
	el => 
	  val elt = el.trim
	  val posFstLetter = elt.find(c => c.isLetter) match {
	    case Some(x) => elt.indexOf(x)
	    case None => elt.length 
	  }
	  val parname = elt.drop(posFstLetter)
	  val parval = elt.take(posFstLetter)
	  //println("*" + el + "*")
	  (parname, parval)
      }
      val n = paramvals.length
      val res = (for(i <- (0 to n-2)) yield (paramvals(i)._1, paramvals(i+1)._2)).toMap
      println(res)
      res
      //Map("alpha2" -> 0, "beta2" -> -2, "eta2" -> -1, "gamma2" -> -2, "eta1" -> -1, "beta1" -> -1, "gamma1" -> -1, "alpha1" -> 0)
    }
  }

  def genZ3VarDecl(x0: String) = {
    val x = if (x0.startsWith("var")) x0.drop(3).trim else x0
    x + " = Int(\'" + x + "\')\n"
  }

  def genZ3VarLocDecl(x0: String) = {
    val x = if (x0.startsWith("var ")) x0.drop(4) else x0
    x + " = Bool(\'" + x + "\')\n"
  }

  def imiDecl2Z3Decl(imiFile: String) = {
     val file = Path.fromString(imiFile)
     val lines = file.lines()
     //a set of Forall, Exists declarations
     var declS = Set[String]()
     //the set of params
     lines foreach {
       l =>
	 val lt = l.trim()
	 //line is of form: loc <loc_name>:
	 if (lt.startsWith("loc "))	 
	   declS += genZ3VarLocDecl(lt.drop(4).split(":")(0).trim)
	 else if (lt.contains(":"))
	   if (lt.contains("parameter")) {
	     val params = lt.split("parameter")(0).split(":")(0).split(",")
	     params.map(x => genZ3VarDecl(x.trim)) foreach {
	       el =>
		 declS += el
	     }
	   }
	   if (lt.contains("clock")) {
	     val clks = lt.split("clock")(0).split(":")(0).split(",")
	     clks.map(x => genZ3VarDecl(x.trim)) foreach {
	       el =>
		 declS += el
	     }	      
	   }
	   if (lt.contains("analog")) {
	     val analogs = lt.split("analog")(0).split(":")(0).split(",")
	     analogs.map(x => genZ3VarDecl(x.trim)) foreach {
	       el =>
		 declS += el
	     }	      
	   }
     }
     declS.foldLeft("")((r,c) => r + "\n" + c) + "\n"
   }

  //duplicate code for the moment (these methods are also in graphZoneVV; need to restructure!!!!
  def mkConjZ3Temp(l: List[String]) = {
    if (l.length > 1) 
      "And(" + l.reduce(_+ ", " +_) + ")"
    else if (l.length == 1) 
      l(0)
    else ""
  }

  def mkDisjZ3Temp(l: List[String]) = {
    if (l.length > 1) 
      "Or(" + l.reduce(_+ ", " +_) + ")"
    else if (l.length == 1) 
      l(0)
    else ""
  }

  /** transforms the content from statesFile into a formula for Z3
    * @param statesFile is the file name f.states file resulted from calling imitator on f.imi
    * 
    */ 
  def states2CIZ3(statesFile: String)(implicit clksL: Set[String]=Set()) = {
    val file = Path.fromString(statesFile)
    val lines = file.lines()
    //the resulting component invariant
    var conjL = List[String]()
    var disjL = List[String]()
    var kpL = List[String]()
    var zone = ""

    lines foreach {
      l =>
	val lt = l.trim()
	if (//!lt.startsWith("/") && 
	    //!lt.startsWith("*") && 
	    !lt.startsWith("DESCRIPTION") && 
	    !lt.startsWith("STATE") && 
	    !lt.contains(" via ") &&
	    !lt.equals("\n")) {
	      //line of form: <TA_NAME>:<LOC_NAME> ==>
	      if (lt.contains(":") && lt.contains("==>")) {	
		// a new symbolic state is found; generate Kp for the previous one
                if (zone != "") 
	     		kpL :+= "Tactic('qe2').apply(Exists([" + clksL.reduceLeft(_+","+_) + "], And(" + zone.dropRight(1) + "))).as_expr()"
               
                 zone = "" 
		//val loc = lt.split(":")(1).split("==>")(0).trim 
		val locs = lt.split("==>")(0).trim.split(",").map{_.trim.split(":")(1).trim}.reduceLeft(_+", "+_) 
		val c = mkConjZ3Temp(conjL)
		if (c != "")
		  disjL = disjL :+ c
		conjL = List(locs)
	      }
	      if (lt.startsWith("&")) {
		//line of form: & term1 op term2 where op \in {>=, =}
		val ct = lt.drop(1).replace(" = ", " == ")   
		if (ct.trim != "true") {
		  conjL = conjL :+ ct
		  zone += ct + ","
		}
	      }	    
	    }
    }
    val lastc = mkConjZ3Temp(conjL)
    if (lastc != "")
      disjL = disjL :+ lastc
    (mkDisjZ3Temp(disjL), mkConjZ3Temp(kpL))
  }

}

