package maf.lattice.interfaces

import maf.core.Lattice

/** A lattice for integers */
trait IntLattice[I] extends Lattice[I, BigInt] { self =>
    def inject(n: BigInt): I

    def toReal[R: RealLattice](n: I): R
    def random(n: I): I
    def plus(n1: I, n2: I): I
    def minus(n1: I, n2: I): I
    def times(n1: I, n2: I): I
    def quotient(n1: I, n2: I): I
    def div[R: RealLattice](n1: I, n2: I): R
    def expt(n1: I, n2: I): I
    def modulo(n1: I, n2: I): I
    def remainder(n1: I, n2: I): I
    def lt[B: BoolLattice](n1: I, n2: I): B
    def valuesBetween(n1: I, n2: I): Set[I]
    def makeString[C: CharLattice, S: StringLattice](length: I, char: C): S
    def toString[S: StringLattice](n: I): S
    def toChar[C: CharLattice](n: I): C
}

object IntLattice:
    def apply[I: IntLattice]: IntLattice[I] = implicitly
