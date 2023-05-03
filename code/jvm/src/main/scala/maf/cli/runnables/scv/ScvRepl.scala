package maf.cli.runnables.scv

import maf.util.benchmarks.Table
import maf.cli.experiments.SchemeAnalyses
import maf.cli.modular.scv.JVMSatSolver

import scala.io.StdIn.readLine
import maf.language.ContractScheme.*
import maf.language.scheme.{ContractSchemeContractOut, SchemeAnd, SchemeAssert, SchemeBegin, SchemeDefineFunction, SchemeDefineVariable, SchemeExp, SchemeFuncall, SchemeIf, SchemeLambda, SchemeLet, SchemeOr, SchemeSet}
import maf.language.symbolic.{Conjunction, Formula, Implication}
import maf.util.benchmarks.Timeout
import maf.modular.scheme.modf.SchemeModFComponent
import maf.modular.scheme.SchemeConstantPropagationDomain
import maf.modular.scv.{Sat, ScvReporter, Unknown, Unsat}
import maf.util.Reader

import scala.collection.mutable.ListBuffer

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

    val solver = new JVMSatSolver[analysis.Value](analysis)(using analysis.lattice)
    var toDelete = List[Formula]()

    // loop over all pathconditions in the map
    for ((schemeExp, formula) <- analysis.pathConditions) {
      var currentFormula = formula

      // loop over all conditions in the formula
      for (condition <- formula.splitConj) {
        val newFormula = Conjunction(formula.elements - condition)

        //create an implication of the newFormula and the original formula
        val implication = Implication(newFormula, currentFormula)

        // Does the new formula imply the original formula?
        solver.sat(implication, implication.variables) match {
          case Sat(_) =>
            // if sat, the condition is redundant, delete it, add it to deleted list
            currentFormula = newFormula
              toDelete = condition :: toDelete

          case Unsat =>
          // if unsat, don't delete, check next condition
          case Unknown =>
          // if unknown, to play it 'safe' same as unsat
        }
      }

      // replace the formula in the map
      analysis.pathConditions = analysis.pathConditions + (schemeExp -> currentFormula)
    }

      // remove all assertions to immediately have the schemeExp's
      toDelete = toDelete.map {
          case assertion(exp) => exp
          case other => other
      }
      // check for pairs of conditions that negate each other
      //create separate lists for conditions that are true and false

      //Ik denk dat ik "_" moet invullen als het niet uitmaakt wat er daar staat?
      val trueConditions = toDelete.filter(_ == SchemeFuncall(SchemeVar(identifier("true?", idn)), _, _))

      val falseConditions = toDelete.filter(_ == SchemeFuncall(SchemeVar(identifier("false?", idn)), _, _)))

      //for each 'trueCond' in trueConditions, find a false condition in falseConditions with the same tail
      //and make a pair out of it
      val deletePairs = trueConditions.flatMap { trueCond =>
          falseConditions.find(_.elements.tail == trueCond.elements.tail).map(falseCond => (trueCond, falseCond))
      }

      //delete those pairs from the toDelete list
      toDelete --= (deletePairs.map(_._1) ++ deletePairs.map(_._2))


      println(analysis.summary.blames.values.flatten.toSet.size)
    println(analysis.summary.blames.values.flatten.toSet)
    println(analysis.pathConditions)

    println(s"is finished ${analysis.finished} in ${ellapsed / (1000 * 1000)} ms")
    //println(analysis.mapStoreString())
    analysis.returnValue(analysis.initialComponent)

    /*
        ble(name, value, idn) =>
        case SchemeDefineFunction(name, args, body, idn) =>
        case SchemeDefineVarAcase SchemeLambda(name, args, body, ann, idn) =>
        case SchemeVarArgLambda(name, args, vararg, body, ann, idn) =>
        case SchemeFuncall(f, args, idn) =>
        case SchemeIf(cond, cons, alt, idn) =>
        case SchemeLet(bindings, body, idn) =>
        case SchemeLetStar(bindings, body, idn) =>
        case SchemeLetrec(bindings, body, idn) =>
        case SchemeSet(variable, value, idn) =>
        case SchemeSetLex(variable, lexAddr, value, idn) =>
        case SchemeBegin(exps, idn) =>
        case SchemeDefineVariargFunction(name, args, vararg, body, idn) =>
        case SchemeVar(id) =>
        case SchemeVarLex(id, lexAdr) =>
        case SchemeValue(value, idn) =>
     */

    def deleteFromAST(ast: SchemeExp, toDelete: List[Formula]): SchemeExp = {

        def deleteFromExp(exp: SchemeExp, toDelete: ListBuffer[Formula]): SchemeExp = {
            exp match {

                case SchemeAssert(assertion, idn) =>
                    SchemeAssert(deleteFromExp(assertion, toDelete), idn)

                case SchemeDefineVariable(name, value, idn) =>
                    SchemeDefineVariable(name, deleteFromExp(value, toDelete), idn)

                case SchemeLambda(name, args, body, ann, idn) =>
                    SchemeLambda(name, args, deleteFromExp(body, toDelete), ann, idn)

                case SchemeBegin(exps, idn) =>
                    val newExps = exps.map(deleteFromExp(_, toDelete))
                    SchemeBegin(newExps, idn)

                    //hierin gebeurd ook schemeand en schemeor
                case SchemeIf(cond, cons, alt, idn) =>
                    SchemeIf(deleteFromExp(cond, toDelete),
                        deleteFromExp(cons, toDelete),
                        deleteFromExp(alt, toDelete), idn)

                case SchemeSet(variable, value, idn) =>
                    SchemeSet(variable, deleteFromExp(value, toDelete))

                //recursivly call 'deletefromexp' on the bindings to update the bindings
                //then recursivly call on the body to also update the body
                case SchemeLet(bindings, body, idn) =>
                    val newBindings = bindings.map { case (v, e) => (v, deleteFromExp(e, toDelete)) }
                    SchemeLet(newBindings, deleteFromExp(body, toDelete), idn)

                    // inner-case om  voor > , < , = te matchen
                case SchemeFuncall(f, args, idn) =>
                    //Ik check enkel of het true of false is ik ga niet na of het '> , <, =' is
                    //want ik hoef eigenlijk niet te weten wat de conditie is
                    f match {
                        case SchemeVar(Identifier("true?", idn)) =>
                            toDelete match{
                                //SchemeValue(SexpValue...
                                case SchemeFuncall(SchemeVar(identifier("true?", idn)), _, idn)) =>
                                    SchemeFuncall(SchemeVar(identifier("true?", idn)),SchemeValue(Value.Boolean(true), NoCodeIdentity),idn)
                            }
                        case SchemeVar(Identifier("false?", idn)) =>
                            toDelete match {
                                case SchemeFuncall(SchemeVar(identifier("false?", idn)), _, idn)) =>
                                    SchemeFuncall(SchemeVar (identifier ("false?", idn) ),SchemeValue(Value.Boolean(false), NoCodeIdentity), idn)
                            }
                    }

                case ContractSchemeContractOut(name, contract, idn) =>
                    ContractSchemeContractOut(name, deleteFromExp(contract, toDelete), idn)

                case ContractSchemeDepContract(domains, rangeMaker, idn) =>
                    val newDomains = domains.map(deleteFromExp(_, toDelete))
                    val newRangeMaker = deleteFromExp(rangeMaker, toDelete)
                    ContractSchemeDepContract(newDomains, newRangeMaker, idn)

                case ContractSchemeFlatContract(expression, idn) =>
                    val newExpression = deleteFromExp(expression, toDelete)
                    ContractSchemeFlatContract(newExpression, idn)

                case ContractSchemeMon(contract, expression, idn) =>
                    val newContract = deleteFromExp(contract, toDelete)
                    val newExpression = deleteFromExp(expression, toDelete)
                    ContractSchemeMon(newContract, newExpression, idn)

                case ContractSchemeDefineContract(name, params, contract, expression, idn) =>
                    val newContract = deleteFromExp(contract, toDelete)
                    val newExpression = deleteFromExp(expression, toDelete)
                    ContractSchemeDefineContract(name, params, newContract, newExpression, idn)

                case ContractSchemeCheck(contract, valueExpression, idn) =>
                    val newContract = deleteFromExp(contract, toDelete)
                    val newValueExpression = deleteFromExp(valueExpression, toDelete)
                    ContractSchemeCheck(newContract, newValueExpression, idn)

                case ContractSchemeProvide(outs, idn) =>
                    val newOuts = outs.map { out =>
                        val newOutExpression = deleteFromExp(out.expression, toDelete)
                        ContractSchemeProvideOut(newOutExpression, out.provides)
                    }
                    ContractSchemeProvide(newOuts, idn)

                case _ => exp
            }
            }
        }



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


  repl()
