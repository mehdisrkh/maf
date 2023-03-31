package maf.cli.runnables.scv

import maf.util.benchmarks.Table
import maf.cli.experiments.SchemeAnalyses

import scala.io.StdIn.readLine
import maf.language.ContractScheme.*
import maf.util.benchmarks.Timeout
import maf.modular.scheme.modf.SchemeModFComponent
import maf.modular.scheme.SchemeConstantPropagationDomain
import maf.modular.scv.ScvReporter
import maf.util.Reader

object ScvRepl extends App:
  def analyse(program: String): Any =
    val exp = ContractSchemeParser.parse(program.nn)
    println(s"parsed expression $exp")
    //val analysis = SchemeAnalyses.scvModAnalysisWithRacketFeatures(exp)
    val analysis = SchemeAnalyses.scvModAnalysisRktFsR(exp)
    //val analysis = SchemeAnalyses.scvModAnalysisFunctionSummary(exp)
    //val analysis = SchemeAnalyses.scvModAnalysisFunctionSummaryTopSort(exp)
    val (ellapsed, _) = maf.util.benchmarks.Timer.time {
      analysis.analyze()
    }
    println(analysis.summary.blames.values.flatten.toSet.size)
    println(analysis.summary.blames.values.flatten.toSet)
    println(analysis.pathConditions)

    println(s"is finished ${analysis.finished} in ${ellapsed / (1000 * 1000)} ms")
    //println(analysis.mapStoreString())
    analysis.returnValue(analysis.initialComponent)

  def repl(): Unit =
    print(">")
    val program = readLine().trim().nn
    if program.startsWith(":f") then
      val args = program.replace(":f", "").nn.trim().nn
      val filename = args
      println(analyse(Reader.loadFile(filename)))
      repl()
    else if program != ":q" then
      println(analyse(program))
      repl()

  object MyModReporter extends ScvReporter //(Mehdi)

  val solver = JVMSatSolver(MyModReporter)

  // loop over all pathconditions in the map
  for ((schemeExp, formula) <- pathConditions) {
    var currentFormula = formula
  
    // loop over all conditions in the formula
    for (condition <- formula.splitConj) {
      val newFormula = Conjunction(formula.elements - condition) /// mag dit? stel ook disjuncties?
  
      //create an implication of the newFormula and the original formula
      val implication = Implication(newFormula, currentFormula)
  
      // Does the new formula imply the original formula?
      solver.sat(implication, implication.variables) match {
        case Sat =>
          // if sat, the condition is redundant, delete it
          currentFormula = newFormula
        case Unsat =>
        // if unsat, don't delete, check next condition
        case Unknown =>
        // if unknown, to play it 'safe' same as unsat
      }
    }
  
    // replace the formula in the map
    pathConditions = pathConditions + (schemeExp -> currentFormula)
  }


repl()
