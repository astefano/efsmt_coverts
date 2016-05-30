package org

import parma_polyhedra_library._

object TestPPL extends ZoneGraphVV {

  def main(args: Array[String]) {

    Parma_Polyhedra_Library.initialize_library()   
    
    val z = new Variable(0)    
    val le_z = new Linear_Expression_Variable(z)
    val p = new Variable(1)    
    val le_p = new Linear_Expression_Variable(p)
    val dim = 2 
    val coeff_2 = new Coefficient(2)
    val le_2 = new Linear_Expression_Coefficient(coeff_2)
    val coeff_5 = new Coefficient(5)
    val le_5 = new Linear_Expression_Coefficient(coeff_5)
    val g = new NNC_Polyhedron(dim, Degenerate_Element.UNIVERSE)
    //g.add_constraint(new Constraint(le_z, Relation_Symbol.LESS_OR_EQUAL, le_p))
    g.add_constraint(new Constraint(le_z, Relation_Symbol.EQUAL, le_5))
    g.add_constraint(new Constraint(le_z, Relation_Symbol.GREATER_OR_EQUAL, le_2))

    
    flashBwd(g, Set(z,p)) 
   
    Parma_Polyhedra_Library.finalize_library()

  }
}

