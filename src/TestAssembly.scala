package org

import parma_polyhedra_library._
import scalax.io._
import scalax.file.{ FileOps, Path, NotFileException }
import java.io.FileNotFoundException

object TestAssembly extends genEF {

  def main(args: Array[String]) {

    val userdir = System.getProperty("user.dir")
    val modelPath = userdir + "/" + "Imitator/Philos2"
    var outEF = ""
    try {
      val dir = new java.io.File(modelPath)    
      dir.listFiles.filter(f => !f.isDirectory).map(f => f.toString).filter(fs => fs.endsWith(".imi")).toList.map{
	file => 
	val out = runImitator(file) 
	outEF += "\n" + imiDecl2EFDecl(file) + "\n\n" + states2CIEF(out)
      }
	println(outEF)

        val filePath = userdir + "/out/Philos2.out.efsmt" 
	println("result written to file = " + filePath)
	val path = Path.fromString(filePath)
        path.createFile(failIfExists=false)
        val filer: FileOps = Path.fromString(filePath)		   
       // By default the file write will replace
       // an existing file with the new data
       filer.write (outEF)
    }  


  }
}


