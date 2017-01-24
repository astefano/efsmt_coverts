===================
Short Description: 
===================

This is a Scala prototype for synthesising parameters for parametric timed systems. The prototype takes as input:
- components $\cn_i$ of a system as PTAs in Imitator, 
- a file describing the interactions $\gamma$ (each interaction is on one line with actions being separated by comma), 
- a state safety formula (if not specified, by default deadlock freeness as defined in \cite{tripakis93:progress}). 
Constraints on parameters are specified directly in the Imitator files. 

The prototype uses EFSMT and Z3 to return either \texttt{unsat} or a parameter assignment under which the safety property holds. The prototype reuses functionalities from the prototype in \cite{abbbc14} to compute $\iim(\gamma)$ and $\eqs(\gamma)$. The computation of $\sep(\gamma)$ by means of the observer construction is not implemented yet. To generate $\ic(\cn_i^h)$ we use Imitator. From all invariants we assemble $\isyst$ which with the parameter constraints and the safety formula are fed to EFSMT \cite{efsmt} and Z3 \cite{z3}. We did not explicitly do quantifier elimination but instead quantified universally all history clocks. For the extraction of parameter constraints we used the tactic $\texttt{qe2}$ in Z3. 

==========================
Installation Requirements: 
==========================

- Z3 (z3.codeplex.com) 
- EFSMT (http://www6.in.tum.de/~chengch/efsmt/)
- IMITATOR (https://github.com/etienneandre/imitator) 
- sbt (http://www.scala-sbt.org/) 
- PPL (bugseng.com/products/ppl/‎), the platform dependent libppl_java.so, ppl_java.jar must be copied inside the "lib" folder; this is needed for the translation from a PTA C to C^h and for the computation of enabled. 

(The binaries from EFSMT and IMITATOR should be placed in a folder "dependencies" if not specified as arguments, see below.)

=============
How to test: 
=============

The main program is src/PTAG2EF.scala. You can either pass the path to the Imitator files and to the interaction model as arguments or directly modify PTAG2EF.scala itself (examples are commented). Then simply run it from sbt.

Example:

lacra@lacra-VirtualBox:~/tools/efsmt_coverts-master$ sbt

efsmt_coverts> run -ptaDir imitator_examples/Imitator/abstract2 -imFile imitator_examples/interactionModels/abstract2.im 

Other examples are in imitator_examples. 

=============================
Usage: parse info:  [options]
=============================

  	 -ptaDir <ptaDir> | --ptaDir <ptaDir>

  	 	 ptaDir is the relative path to the dir with models

  	 -imFile <imFile> | --interactionModelFile <imFile>

  	 	 the relative path to the file with the interaction model

  	 -hc <hc> | --historyClocks <hc>

  	 	 reach with history clocks

  	 -ip <value> | --imitatorPath <value>

  	 	 imitatorPath is the absolute path to Imitator (if not specified, by default, it's expected to be in folder dependencies)

  	 -efp <value> | --EFSMTPath <value>

  	 	 EFSMTPath is the absolute path to EFSMT (if not specified, by default, it's expected to be in folder dependencies)

