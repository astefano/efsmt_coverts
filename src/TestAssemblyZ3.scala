package org

import parma_polyhedra_library._

object TestAssemblyZ3 extends genZ3EF {

  def main(args: Array[String]) {

    val modelPath = System.getProperty("user.dir") + "/" + "hymitator_examples/TankEx"
    try {
      val dir = new java.io.File(modelPath)    
      dir.listFiles.filter(f => !f.isDirectory).map(f => f.toString).filter(fs => fs.endsWith(".hym")).toList.map{
	file => 
	val out = runHymitator(file) 
	println("out = " + out)
	val outZ3 = "\n" + imiDecl2Z3Decl(file) + "\n\n" + "Inv" + file.dropRight(4).reverse.takeWhile(_!="\\").reverse + " = " + states2CIZ3(file + ".states") + "\n"
	println(outZ3)
      }
    }  


  }
}


