package org

import parma_polyhedra_library._
import scalax.io._
import scalax.file.{ FileOps, Path, NotFileException }
import java.io.FileNotFoundException


object TestAssemblyZ3 extends genZ3EF {

  def main(args: Array[String]) {

    val userdir = System.getProperty("user.dir")
    val modelPath = userdir + "/" + "Imitator/Philos2"
    var outZ3 = ""
    try {
      val dir = new java.io.File(modelPath)    
      dir.listFiles.filter(f => !f.isDirectory).map(f => f.toString).filter(fs => fs.endsWith(".imi")).toList.map{
	file => 
        val fn = file.toString.dropRight(4)
	val out = runImitator(file) 
	outZ3 += "\n" + imiDecl2Z3Decl(file) + "\n\n" + "Inv_" + file.dropRight(4).reverse.takeWhile(_!='/').reverse + " = " + states2CIZ3(fn + ".states") + "\n"
      }
     println(outZ3)

     val filePath = userdir + "/out/Philos2_z3.py" 
     println("result written to file = " + filePath)
     val path = Path.fromString(filePath)
     path.createFile(failIfExists=false)
     val filer: FileOps = Path.fromString(filePath)		   
     // By default the file write will replace
     // an existing file with the new data
     filer.write (outZ3)
    }  
    //val modelPath = System.getProperty("user.dir") + "/" + "hymitator_examples/TankEx
  }
}


