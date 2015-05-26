package org

import parma_polyhedra_library._

//for parsing
import scala.util.parsing.combinator.PackratParsers
import scala.util.parsing.combinator.RegexParsers
import scala.util.parsing.combinator._

import scala.util.matching.Regex

//options parser
import scopt._

object GenUppaal extends ZoneGraphVV {

  def main(args: Array[String]) {
    var badArgs = false
    var ptaDir = ""
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
    }

    require (parser.parse(args) && !badArgs, println("error while parsing arguments for TA."))  

    Parma_Polyhedra_Library.initialize_library()   

    val modelPath = wd + ptaDir 
    try {
      val dir = new java.io.File(modelPath)    
      dir.listFiles.filter(f => !f.isDirectory).map(f => f.toString).filter(fs => fs.endsWith(".imi")).toList.map{
	filePTA => 
	  val pta = loadImi(filePTA)
	  val ta = getTA(pta)
	  genUppaalTA(ta)
      }
    }
  }
}

