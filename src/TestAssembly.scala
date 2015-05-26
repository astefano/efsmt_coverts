package org

import parma_polyhedra_library._

object TestAssembly extends genEF {

  def main(args: Array[String]) {

    val modelPath = System.getProperty("user.dir") + "/" + "Imitator/Philos2"
    try {
      val dir = new java.io.File(modelPath)    
      dir.listFiles.filter(f => !f.isDirectory).map(f => f.toString).filter(fs => fs.endsWith(".imi")).toList.map{
	file => 
	val out = runImitator(file) 
	val outEF = "\n" + imiDecl2EFDecl(file) + "\n\n" + states2CIEF(out)

	println(outEF)
      }
    }  


  }
}


