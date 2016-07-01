package org

import parma_polyhedra_library._

//for parsing
import scala.util.parsing.combinator.PackratParsers
import scala.util.parsing.combinator.RegexParsers
import scala.util.parsing.combinator._

import scala.util.matching.Regex

//options parser
import scopt._

object PTAG2EF extends ZoneGraphVV {

  def main(args: Array[String]) {

    //runConfig(configFile)
    var badArgs = false

    val ImitatorEx = "imitator_examples/Imitator"

    //var ptaDir = ImitatorEx + "/Philos2"
    //var ptaDir = ImitatorEx + "/abstract8"
    //var ptaDir = ImitatorEx + "/abstract2"
    var ptaDir = ImitatorEx + "/tgc"
    //var ptaDir = "Imitator/tc"

    var imFile = ""
    //var imFile = "interactionModels/philos2.im"
    //var imFile = "interactionModels/abstract8.im"
    //var imFile = "interactionModels/abstract2.im"

    //val im = mkIM(wd + imFile)
    def genIM_TGC(n: Int) = List.range(0,n).flatMap{i => List(List("ac", "at_"+i), List("ec", "et_"+i), List("lc", "lg"), List("rc", "rg"), List("epst_"+i))} :+ List("epsg")
    var im = genIM_TGC(16).map{_.toSet}.toSet

    def genIM_TC(n: Int) = List.range(0,n).flatMap{i => List(List("coolc", "cool_"+i), List("restc", "rest_0"))} 
    //var im = genIM_TC(32).map{_.toSet}.toSet

    var withHC = true
    //var withHC = false

    val parser = new OptionParser("parse info: ") {      
       opt("ptaDir", "ptaDir", "<ptaDir>", "ptaDir is the relative path to the dir with models", { 
	 v: String => ptaDir = v
       })

       opt("imFile", "interactionModelFile", "<imFile>", "the relative path to the file with the interaction model", { 
	 v: String =>  imFile = v
       })

       opt("hc", "historyClocks", "<hc>", "reach with history clocks", {
	 v: String => withHC = true	 
       })

       opt("ip", "imitatorPath", "imitatorPath is the absolute path to Imitator (if not specified, by default, it's expected to be in folder dependencies)", { 
	 v: String => IMITATORPATH = v
       })

       opt("efp", "EFSMTPath", "EFSMTPath is the absolute path to EFSMT (if not specified, by default, it's expected to be in folder dependencies)", { 
	 v: String => EFSMTPATH = v
       })

       opt("h", "help", "prints this usage text", {println(
	 "\n Usage: parse info:  [options]" + 
	 "\n" + 
	 "\n \t -ptaDir <ptaDir> | --ptaDir <ptaDir>" +
	 "\n \t \t ptaDir is the relative path to the dir with models" +
	 "\n \t -imFile <imFile> | --interactionModelFile <imFile>" +
	 "\n \t \t the relative path to the file with the interaction model" + 
	 "\n \t -hc <hc> | --historyClocks <hc>" +
	 "\n \t \t reachability with history clocks" + 
	 "\n \t -ip <value> | --imitatorPath <value>" +
	 "\n \t \t imitatorPath is the absolute path to Imitator (if not specified, by default, it's expected to be in folder dependencies)" +
	 "\n \t -efp <value> | --EFSMTPath <value>" +
	 "\n \t \t EFSMTPath is the absolute path to EFSMT (if not specified, by default, it's expected to be in folder dependencies)"
       )})
    }

    parser.parse(args)

    //var im = mkIM(wd + imFile)
    println("im = " + im)

    var z3CI = ""
    var outZ3 = ""

    var outEF = ""
    var paramSet = Set[String]()

    var tas : TAS = List[TA]()
    var tasName = ""
    var taName = ""

    var decl = ""
    var paramsC = Set[String]()
    Parma_Polyhedra_Library.initialize_library()   

    val modelPath = wd + ptaDir 
    try {
      val dir = new java.io.File(modelPath)    
      dir.listFiles.filter(f => !f.isDirectory).map(f => f.toString).filter(fs => fs.endsWith(".imi")).toList.map{
	filePTA => 
	  val pta = loadImi(filePTA)
	var ta = getTA(pta)
        println("ptag2ef for file " + filePTA + " ta = " + ta)
	val params = getParams(pta)
        var out = ""
        //[TODO:] only do HC if pta has clks; need to chg the generation of eqs, i.e., don't generate = h_a if a is an action in a component without clks
        val hasClks = getClkMap(ta).size > 0         
	if (withHC) { // && hasClks) {
		val tah = getTAH(ta)
                ta = tah
		val ptah = getPTA(tah, params)
		val modelPathH = modelPath + "H/"
		//println("pta: " + pta)
		println("ptaH: " + ptah)
		mkImi(ptah, modelPathH)
		val filePTAH = modelPathH + getName(tah) + ".imi"	    	  
		out = runImitator(filePTAH) 
                val r = imiDecl2EFDecl(filePTAH) 
		decl = r._1 
		paramsC = r._2
	        paramSet ++= paramsC
                tas = tas:+ tah 
		taName = getName(tah) + "h"
		tasName += taName + "_" 
		val eqs = getEqsSimpl(im.map{_.toList}.toList, false)    
                outEF += "\nAssumption(" + eqs + ")\n"
        }
        else {
                out = runImitator(filePTA)
                val r = imiDecl2EFDecl(filePTA) 
		decl = r._1 
		paramsC = r._2
    	        paramSet ++= paramsC
                tas = tas:+ ta 
		taName = getName(ta)
		tasName += taName + "_" 
        }
	outEF += "\n" + decl + "\n\n" + states2CIEF(out)
	//get the Z3 CI for the pta with histories
	//UGLY: hard encoded path
         
	//z3CI = "\nci" + taName + " = " + "And(" + states2CIZ3(out) + ", " + genNotAt2LocsTA(ta) + ")" + "\n"
        val (ci, kp) = states2CIZ3(out)(getClks(ta).toSet.diff(getParams(pta)))
        z3CI = "\nci" + taName + " = " + ci + "\n"
        val notAt2Locs = "\n" + NotAt2LocsPref + taName + "  = " +  genNotAt2LocsTA(ta) + "\n"
	outZ3 += z3CI 
	outZ3 += notAt2Locs	
        val kpN = "\n" + Kp + taName + " = " + kp + "\n"
        outZ3 +=  kpN
      }
    }
   
/*
    val additionalAssumptions = mkEFAssumption(mkIneq("ts1 == ts2")) + "\n" 
				mkEFAssumption(mkIneq("ts2 == ts3")) +  "\n" + 
				//mkEFAssumption(mkIneq("ts3 == ts4")) +  "\n" +
				mkEFAssumption(mkIneq("ts3 == ts1")) 

    outEF += "\n\n" + additionalAssumptions + "\n"
*/

    val (absReach_EnEF, absReach_EnZ3) = genAbsReach_EnEFZ3(tas, im)
    outEF += absReach_EnEF
   
    outZ3 += absReach_EnZ3

    println("outz3=" + outZ3) 	    
/*  
    //dirty: will be passed as param 
    
    var appSpecificConds = "Condition([gamma1 >=  eta1])\n" +
			   "Condition([gamma2 >=  eta2])\n" +
			   "Condition([alpha1 > beta1])\n" +
			   "Condition([alpha2 >= beta2])\n" + 
			   "Condition([eta1 > eta2])\n" +
			   "Condition([gamma1 > gamma2])\n" + 
			   "Condition([alpha1 > 10])\n" 
			  /* "Condition([gamma3 >=  eta3])\n" +
			   "Condition([gamma4 >=  eta4])\n" +
			   "Condition([alpha3 > beta3])\n" +
			   "Condition([alpha4 >= beta4])\n" + 
			   "Condition([eta3 > eta4])\n" +
			   "Condition([alpha3 > 10])\n" + 
			   "Condition([gamma5 >=  eta5])\n" +
			   "Condition([alpha5 > beta5])\n" */


    outEF += appSpecificConds
*/
    //add the initial conditions: all params > 0
    val outEFWithConds = outEF + mkEFCondFromParams(paramSet.map{p => (p -> "0")}.toMap)

    import java.util.Calendar
    import java.text.SimpleDateFormat

    val today = Calendar.getInstance.getTime
    val curTimeFormat = new SimpleDateFormat("D_M_Y")

    val date = curTimeFormat.format(today)

    //val efFile = tasName + "-outEF-" + date
    val efFile = ptaDir.drop(9) + "-outEF-" + date
    write2File(efFile, outEFWithConds)
    
    
    // if not withHC get the tas with hc for z3
    val tasH = if (withHC) tas.map{ta => getTAH(ta)} else tas
    val deltas = Map[String,Int]()
    println("#deltas = " + deltas)
    //transf im to a list of lists for genTCZ3
    val imL = im.map{_.toList}.toList
    //TODO translate absReach to Z3
    //val absReach = absReach_En._1
    //val z3Txt = genTCZ3(tasH, im, deltas, "", "defaultZ3.py", "", abstractReach, true)
    //no II for the moment
    //val z3Txt = genTCZ3(s=tasH, im0=imL, portDelays=deltas, dis0="", "defaultZ3.py")
    val z3Txt = genZ3forPTA(tasH, imL, deltas, defaultZ3FileName="defaultZ3.py", defaultInvs=outZ3, paramsS = paramSet)(withHC)
    //val z3File = tasName + "-outZ3-" + date + ".py"
    val z3File = ptaDir.drop(9) + "-outZ3-" + date + ".py"      

    val efFilePath = wd + efFile
    //addEFConds(efFilePath, paramsVals)
    var sat = true
    var ntries = 0
    while(sat && ntries < 1) {
      var paramVals = runEF(efFilePath)
      if (paramVals.size == 0) { 
	sat = false
	write2File(wd + z3File, z3Txt)
	}
      else {
	val strengthen = if (paramVals.size != 0) "And(" + paramVals.foldLeft("")((r,c)=>r + ", " + c._1 + " == " + c._2).drop(2) + ")" else ""
	
	val z3TxtWithParams = addStrengthen(z3Txt, strengthen)       

	write2File(wd + z3File, z3TxtWithParams)
	val (resultZ3, errZ3) = runZ3(z3File)	
	if (errZ3.contains("error") || errZ3.contains("Error")) {
	  println("Z3 err: " + errZ3 + "; exit.")
	  System.exit(1)
	}
	sat = !resultZ3.contains("no solution")
	if (sat) {
	  //add conditions wrt params
	  val cexParams = getCEXParamsFromZ3(resultZ3, paramSet)
	  println("cexParams = " + cexParams)
	  val outEFwithNewParams = outEF + mkEFCondFromParams(cexParams)
	  write2File(efFile, outEFwithNewParams)
	}
	else {
	  println("Z3 finds no cex for the following param values: " + paramVals + "; reuse those from EFSMT with strict >.")
	  //check if paramVals makes a component inv false
	  val outEFwithNewParams = outEF + mkEFCondFromParams(paramVals, ">")
	  write2File(efFile, outEFwithNewParams)
	} 
      }
      ntries += 1
    }

    Parma_Polyhedra_Library.finalize_library()

  }
}

