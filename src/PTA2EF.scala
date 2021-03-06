package org

import parma_polyhedra_library._

//for parsing
import scala.util.parsing.combinator.PackratParsers
import scala.util.parsing.combinator.RegexParsers
import scala.util.parsing.combinator._

import scala.util.matching.Regex

//options parser
import scopt._

object PTA2EF extends ZoneGraphVV {

  def getBit(x: Int, i: Int) = if ((x & (1 << i)) != 0) 1 else 0

  def encodeLocs(ta: TA) = {
    val locs = getLocs(ta).toList.sorted
    val name = getName(ta)
    val defaultlocname = "l" + name
    val n = locs.length

    if (n == 2) {
      (Map((locs(0) -> ("!"+defaultlocname)), (locs(1) -> defaultlocname)), 
       Set(defaultlocname))
    }
    else {
      var nlocs = Set[String](defaultlocname+"0", defaultlocname+"1")
      val map2 = Map[Location, Location]((locs(0), "!"+defaultlocname+"0 && !" +defaultlocname+"1"), 
					 (locs(1), defaultlocname+"0 && !" +defaultlocname+"1"))
      val maplocs = List.range(2, n).map{
	i =>
	  var is = i
	var pos = 0
	var encode = ""
	while (is > 0) {
	  val bit = is & (1 << 0)
	  val neg = if (bit != 0) "" else "!"
	  encode +=  neg + defaultlocname + pos + " && "
	  nlocs += defaultlocname + pos
	  is = is >> 1
	  pos += 1
	}
	((locs(i) -> encode.dropRight(4).trim))
      } ++ map2

      (maplocs.toMap, nlocs)
    }
  }

  def main(args: Array[String]) {

    //runConfig(configFile)
    var badArgs = false

    var ptaDir = ""

    var imFile = ""

    var withHC = false

    val parser = new OptionParser("parse info: ") {
       opt("ip", "imitatorPath", "imitatorPath is the absolute path to imitator", { 
	 v: String => IMITATORPATH = v
       })
      
       opt("ptaDir", "ptaDir", "<ptaDir>", "ptaDir is the relative path to the dir with models", { 
	 v: String => 
	     require(!v.contains("ptaDir"), { 
	       println("Missing value for ptaDir. ")
	       badArgs = true
	     }) 
	 ptaDir = v})

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

    var outEF = ""
    var paramSet = Set[String]()

    var tas : TAS = List[TA]()

    var tasName = ""

    Parma_Polyhedra_Library.initialize_library()   

    val modelPath = wd + ptaDir 
    try {
      val dir = new java.io.File(modelPath)    
      dir.listFiles.filter(f => !f.isDirectory).map(f => f.toString).filter(fs => fs.endsWith(".imi")).toList.map{
	filePTA => 
	  val pta = loadImi(filePTA)
	val ta = getTA(pta)
	val params = getParams(pta)
	val tah = getTAH(ta)
	val ptah = getPTA(tah, params)
	val modelPathH = modelPath + "H/"
	//println("pta: " + pta)
	//println("ptaH: " + ptah)
	mkImi(ptah, modelPathH)
	val filePTAH = modelPathH + getName(tah) + ".imi"	    	  
	val out = if (withHC) runImitator(filePTAH) else runImitator(filePTA)
	val (decl, paramsC) = if (withHC) imiDecl2EFDecl(filePTAH) else imiDecl2EFDecl(filePTA)
	paramSet ++= paramsC
	outEF += "\n" + decl + "\n\n" + states2CIEF(out)
	//get the Z3 CI for the pta with histories
	//UGLY: hard encoded path
	val outPTAH = if (withHC) out else runImitator(filePTAH)
	z3CI = "\nci" + getName(tah) + " = " + states2CIZ3(outPTAH) + "\n"
	outZ3 += z3CI
	tas = tas:+ (if (withHC) tah else ta)
	tasName += (if (withHC) getName(tah) else getName(ta)) + "_" 
      }
    }

    val im = mkIM(wd + imFile)
    //println("im = " + im)

    if (withHC) {
      val eqs = getEqsSimpl(im.map{_.toList}.toList, false)    
      outEF += "\nAssumption(" + eqs + ")\n"
    }

    val additionalAssumptions = mkEFAssumption(mkIneq("ts1 == ts2")) + "\n" 
				mkEFAssumption(mkIneq("ts2 == ts3")) +  "\n" + 
				//mkEFAssumption(mkIneq("ts3 == ts4")) +  "\n" +
				mkEFAssumption(mkIneq("ts3 == ts1")) 

    outEF += "\n\n" + additionalAssumptions + "\n"

    val (absReach_EnEF, absReach_EnZ3) = genAbsReach_EnEFZ3(tas, im)
    outEF += absReach_EnEF
  
    
    outZ3 += absReach_EnZ3
    
    tas foreach {
      ta => 
	val (m, nlocs) = encodeLocs(ta)
	val locs = m.keys.toList
	//replace decl Forall(p._1) 
	val forallOlddecl = locs.map{l => "Forall("+l.trim+")"}
	val forallNewdecl = nlocs.map{l => "Forall("+l.trim+")\n"}.mkString
	outEF = outEF.replace(forallOlddecl(0), forallNewdecl)
	forallOlddecl foreach {
	  d => 
	  outEF = outEF.replace(d, "")
	}
	m foreach {
	  p => 
	    outEF = outEF.replace("Forall(" + p._1 + ")", "").replace(p._1, p._2)
	}
    }
    
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

    //add the initial conditions: all params > 0
    val outEFWithConds = outEF + mkEFCondFromParams(paramSet.map{p => (p -> "0")}.toMap)

    import java.util.Calendar
    import java.text.SimpleDateFormat

    val today = Calendar.getInstance.getTime
    val curTimeFormat = new SimpleDateFormat("D_M_Y")

    val date = curTimeFormat.format(today)

    val efFile = tasName + "-outEF-" + date
    write2File(efFile, outEFWithConds)
    
    
    // if not withHC get the tas with hc for z3
    val tasH = if (withHC) tas else tas.map{ta => getTAH(ta)}
    val philo = tas(0)
    //val rd = computeDelta(philo, "dummyClk")
    //val deltas = rd._2
    val deltas = Map[String,Int]()
    println("#deltas = " + deltas)

    //transf im to a list of lists for genTCZ3
    val imL = im.map{_.toList}.toList
    //TODO translate absReach to Z3
    //val absReach = absReach_En._1
    //val z3Txt = genTCZ3(tasH, im, deltas, "", "defaultZ3.py", "", abstractReach, true)
    //no II for the moment
    //val z3Txt = genTCZ3(s=tasH, im0=imL, portDelays=deltas, dis0="", "defaultZ3.py")
    val z3Txt = genZ3forPTA(tasH, imL, deltas, defaultZ3FileName="defaultZ3.py", defaultInvs=outZ3)
    val z3File = tasName + "-outZ3-" + date + ".py"   

    val efFilePath = wd + efFile
    //addEFConds(efFilePath, paramsVals)
    var sat = true
    var ntries = 0
    while(sat && ntries < 1) {
      var paramVals = runEF(efFilePath)
      if (paramVals.size == 0) 
	sat = false
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

//print simplify(substitute(ciPhilo1h, (beta1, IntVal(0)), (eta1, IntVal(3)), (gamma1, IntVal(3)), (alpha1, IntVal(11))))
