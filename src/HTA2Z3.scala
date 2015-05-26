package org

import parma_polyhedra_library._

//for parsing
import scala.util.parsing.combinator.PackratParsers
import scala.util.parsing.combinator.RegexParsers
import scala.util.parsing.combinator._

import scala.util.matching.Regex

//options parser
import scopt._

//object HA2Z3 extends genZ3EF {
object HA2Z3 extends ZoneGraphVV {

  def main(args: Array[String]) {

    val wd = System.getProperty("user.dir") + "/"

    //runConfig(configFile)
    var badArgs = false

    var haDir = ""

    var imFile = ""

    var withHC = false

    val parser = new OptionParser("parse info: ") {
       opt("hp", "hymitatorPath", "hymitatorPath is the absolute path to hymitator", { 
	 v: String => IMITATORPATH = v
       })
      
       opt("haDir", "haDir", "<haDir>", "haDir is the relative path to the dir with models", { 
	 v: String => 
	     require(!v.contains("haDir"), { 
	       println("Missing value for haDir. ")
	       badArgs = true
	     }) 
	 haDir = v})

       opt("imFile", "interactionModelFile", "<imFile>", "the relative path to the file with the interaction model", { 
	 v: String => 
	     require(!v.contains("imFile"), { 
	       println("Missing value for imFile. ")
	       badArgs = true
	     }) 
	 imFile = v})

       opt("hc", "historyClocks", "<hc>", "reach with history clocks", {
	 v: String => withHC = true	 
       })
    }

    require (parser.parse(args) && !badArgs, println("error while parsing arguments for TA."))  

    var z3CI = ""
    var outZ3 = ""
    var localInvNames = ""

    var tasName = ""

    Parma_Polyhedra_Library.initialize_library()   

    val modelPath = wd + haDir 
    println("modelPath = " + modelPath)
    try {
      val dir = new java.io.File(modelPath)    
      dir.listFiles.filter(f => !f.isDirectory).map(f => f.toString).filter(fs => fs.endsWith(".hym")).toList.map{
	file => 
	  val out = runHymitator(file) 
	  val localInvName = "Inv" + file.dropRight(4).reverse.takeWhile(_!='/').reverse
	  localInvNames += localInvName + ", "
	  outZ3 += "\n" + imiDecl2Z3Decl(file) + "\n\n" + localInvName + " = " + states2CIZ3(file + ".states") + "\n"
      }
    }

    val im = mkIM(wd + imFile)
    //println("im = " + im)

    if (withHC) {
      val eqs = getEqsSimpl(im.map{_.toList}.toList, false)    
      println("eqs = " + eqs)
      outZ3 += "EqsS = " + eqs
    }

    import java.util.Calendar
    import java.text.SimpleDateFormat

    val today = Calendar.getInstance.getTime
    val curTimeFormat = new SimpleDateFormat("D_M_Y")

    val date = curTimeFormat.format(today)
    
    //transf im to a list of lists for genTCZ3
    val imL = im.map{_.toList}.toList

    //ugly; hard-coded prop !!!
    val not2Locs = "Not(Or(And(lc1, lc2), And(l10, l20), And(l11, l21)))"
    outZ3 += "not2Locs = " + not2Locs + "\n"
    val dis = "And(not2Locs, t == M, t0 < T, t1 < T, t0 >= 0, t1 >= 0)"
    outZ3 += "DisN = " + dis + "\n"

    val z3Txt = genZ3fromTxt(localInvNames.dropRight(2), imL, defaultZ3FileName="defaultZ3.py", defaultInvs=outZ3)
    val z3File = modelPath + "-outZ3-" + date + ".py"   
    println("writing to: " + z3File)
    write2File(z3File, z3Txt)

    val (resultZ3, errZ3) = runZ3(z3File)	    
    println("resZ3 = " + resultZ3)
    println("errZ3 = " + errZ3)

    Parma_Polyhedra_Library.finalize_library()

  }
}

//print simplify(substitute(ciPhilo1h, (beta1, IntVal(0)), (eta1, IntVal(3)), (gamma1, IntVal(3)), (alpha1, IntVal(11))))
