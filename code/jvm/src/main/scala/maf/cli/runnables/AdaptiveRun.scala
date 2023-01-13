package maf.cli.runnables

import maf.language.CScheme.CSchemeParser
import maf.language.scheme.SchemeExp
import maf.modular.ReturnAddr
import maf.modular.adaptive.AdaptiveModAnalysis
import maf.modular.adaptive.scheme._
import maf.modular.scheme._
import maf.modular.scheme.modf._
import maf.modular.worklist._
import maf.util.Reader
import maf.util.benchmarks.Timeout
import maf.modular.scheme.modflocal._
import maf.modular.scheme.aam.*

import scala.concurrent.duration._
import scala.language.reflectiveCalls

import maf.cli.experiments.SchemeAnalyses
import maf.language.scheme.interpreter._
import maf.language.scheme.SchemeMutableVarBoxer
import maf.language.scheme.primitives.SchemePrelude
import maf.language.CScheme.CSchemeLexicalAddresser
import maf.core._

object AdaptiveRun:

    def main(args: Array[String]): Unit = print(runDSS(counterExample))

    val prg1 = parse(
        """
        | (define (foo x)
        |    (+ x 1))
        | (define x 5)
        | (foo 1)
        | x
        """.stripMargin
    )

    val counterExample = parse(
        """
        | (let*
        |   ((g (lambda (v) (lambda () v)))
        |    (a (let ((v 100)) (g 42))))
        |   (a))
        """.stripMargin
    )

    def parse(txt: String): SchemeExp =
        val parsed = CSchemeParser.parse(txt)
        val prelud = SchemePrelude.addPrelude(parsed, incl = Set("__toplevel_cons", "__toplevel_cdr", "__toplevel_set-cdr!"))
        val transf = SchemeMutableVarBoxer.transform(prelud)
        CSchemeParser.undefine(transf)

    def runDSS(prg: SchemeExp) =
        val anl = new SchemeDSSAnalysis(prg, 0) with NameBasedAllocator
        anl.analyze()
        val res = anl.results(anl.MainComponent).asInstanceOf[Set[(anl.Val, anl.Dlt, Set[anl.Adr])]]
        val vlu = Lattice[anl.Val].join(res.map(_._1))
        vlu 

    def runAAM(prg: SchemeExp) = 
        val aam = new SchemeAAMAnalysis(prg, 0) with AAMNameBasedAllocator with AAMGC
        aam.analyze()
        aam.finalValue