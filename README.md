===================
Short Description: |
===================

This is a Scala prototype which takes as input components $\cn_i$ of a system as PTAs in Imitator, a file describing the interactions $\gamma$, the constraints over parameters and a safety formula. It returns either \texttt{unsat} or a parameter assignment under which the safety property holds. The prototype reuses functionalities from the prototype in \cite{abbbc14} to compute $\iim(\gamma)$ and $\eqs(\gamma)$. The computation of $\sep(\gamma)$ by means of the observer construction is not implemented yet. To generate $\ic(\cn_i^h)$ we use Imitator. From all invariants we assemble $\isyst$ which with the parameter constraints and the safety formula are fed to EFSMT \cite{efsmt} and Z3 \cite{z3}. We did not explicitly do quantifier elimination but instead quantified universally all history clocks. For the extraction of parameter constraints we used the tactic $\texttt{qe2}$ in Z3. 

==============
Requirements: |
==============

- Z3 (z3.codeplex.com) 
- EFSMT (http://www6.in.tum.de/~chengch/efsmt/)
- IMITATOR (https://github.com/etienneandre/imitator)
- sbt (http://www.scala-sbt.org/) 
- PPL (bugseng.com/products/ppl/‎), the platform dependent libppl_java.so, ppl_java.jar must be copied inside the "lib" folder)

=============
How to test: |
=============

The main program is PTAG2EF.scala. You can either pass the path to the Imitator files and to the interaction model as arguments or directly modify PTAG2EF.scala itself (examples are commented). Then simply run it from sbt.
