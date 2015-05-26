package org

import scalax.io._
import scalax.file.{ FileOps, Path, NotFileException }
import java.io.FileNotFoundException
import scala.util.control.Exception._

import scala.sys.process._

import scala.sys


object RunEFTests extends ZoneGraphVV {

  def main(args: Array[String]) {
    
    val ptaDir = args(0)

    var outTimes = ""

    val modelPath = wd + ptaDir 
    try {
      val dir = new java.io.File(modelPath)    
      println("Inside dir = " + dir)
      dir.listFiles.filter(f => !f.isDirectory).map(f => f.toString) foreach {
	file => 
	  val cmd = ("dependencies/./test " + file)

	  val out = new StringBuilder
	  val err = new StringBuilder

	  val logger = ProcessLogger(
	    (o: String) => out.append(o),
	    (e: String) => err.append(e))

	println("runEFSMT: cmd = " + cmd + "\n\n", 2)
        
	val start = System.currentTimeMillis

	cmd ! logger

	val vt = ( System.currentTimeMillis() - start ) / 1000.0
	outTimes += file + "\n" + out + "\nTime:" + vt + "\n"
	println( "Time (s): " + vt )	
      }
    }
    write2File(ptaDir + "/out.times", outTimes)
  }

}

