package org

import scalax.io._
import scalax.file.{ FileOps, Path, NotFileException }
import java.io.FileNotFoundException
import scala.util.control.Exception._

import scala.sys.process._

import scala.sys

trait genEF {

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
     //println("imidecl2efdecl: paramset = " + paramSet)
     declS.foldLeft("")((r,c) => r + "\n" + c) + "\n" //+ paramSet.foldLeft("")((r,c) => r + "\n" + "Forall(" + c + ")")
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

}

