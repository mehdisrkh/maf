package maf.modular.scheme

import maf.core._
import maf.language.CScheme._
import maf.language.scheme._
import maf.language.scheme.primitives._
import maf.modular._
import maf.modular.scheme._

trait SchemeSetup extends ModAnalysis[SchemeExp] with GlobalStore[SchemeExp]
                                                 with SchemeDomain {
  // Provide a global store
  override var store: Map[Addr, Value] = Map.empty
  // Ensure that the program is translated to use lexical addresses first!
  override lazy val program: SchemeExp = {
    val originalProgram = super.program
    val preludedProgram = SchemePrelude.addPrelude(originalProgram)
    CSchemeUndefiner.undefine(List(preludedProgram))
  }
  lazy val initialBds: Iterable[(String,Addr,Value)] = primitives.allPrimitives.map {
    p => (p.name, PrmAddr(p.name), lattice.primitive(p)) 
  }
  lazy val initialEnv = Environment(initialBds.map(bnd => (bnd._1, bnd._2)))
  // Set up initial environment and install the primitives in the global store.
  initialBds.foreach { bnd => store += bnd._2 -> bnd._3 }
}
