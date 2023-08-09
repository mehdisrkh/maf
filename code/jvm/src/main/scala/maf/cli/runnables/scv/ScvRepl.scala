package maf.cli.runnables.scv

import maf.util.benchmarks.Table
import maf.cli.experiments.SchemeAnalyses
import maf.cli.modular.scv.JVMSatSolver
import maf.core.{Identifier, NoCodeIdentity}

import scala.io.StdIn.readLine
import maf.language.ContractScheme.*
import maf.language.scheme.{ContractSchemeCheck, ContractSchemeContractOut, ContractSchemeDefineContract, ContractSchemeDepContract, ContractSchemeFlatContract, ContractSchemeMon, ContractSchemeProvide, SchemeAnd, SchemeAssert, SchemeBegin, SchemeDefineFunction, SchemeDefineVariable, SchemeExp, SchemeFuncall, SchemeIf, SchemeLambda, SchemeLet, SchemeLetStar, SchemeLetrec, SchemeOr, SchemeSet, SchemeValue, SchemeVar}
import maf.language.sexp.Value
import maf.language.symbolic.{Assertion, Conjunction, Formula, Implication}
import maf.util.benchmarks.Timeout
import maf.modular.scheme.modf.SchemeModFComponent
import maf.modular.scheme.SchemeConstantPropagationDomain
import maf.modular.scv.{Sat, ScvReporter, Unknown, Unsat}
import maf.util.Reader

import scala.collection.mutable.ListBuffer

object ScvRepl extends App:
    def analyse(program: String): Any =
        val exp = ContractSchemeParser.parse(program)
        println(s"parsed expression $exp")
        //val analysis = SchemeAnalyses.scvModAnalysisWithRacketFeatures(exp)
        val analysis = SchemeAnalyses.scvModAnalysisRktFsR(exp)
        //val analysis = SchemeAnalyses.scvModAnalysisFunctionSummary(exp)
        //val analysis = SchemeAnalyses.scvModAnalysisFunctionSummaryTopSort(exp)
        val (ellapsed, _) = maf.util.benchmarks.Timer.time {
            analysis.analyze()
        }

        val solver = new JVMSatSolver[analysis.Value](analysis)(using analysis.lattice)
        var toDelete1: Map[SchemeExp, List[Formula]] = Map()

        println("this is the  PC: ")
        println(analysis.pathConditions)

        // loop over all pathconditions in the map
        for ((schemeExp, formulas) <- analysis.pathConditions) {
            var toDeleteCond: List[Formula] = List.empty
//            println(" for schemeEXP: " + schemeExp + "This is the pc: " + formulas)
            //loop over elke pathconditie van schemeExp
//            println("This is exp: " + schemeExp)
            for (formula <- formulas) {
                var currentFormula = formula
//                println("this is the formula: " + currentFormula)
                // loop over alle conditions in the formula
//                println("this is formula: ")
//                println(formula)
                for (condition <- formula.splitConj) {
//                    println("this is splitconj: " + formula.splitConj)
                    val newFormula = Conjunction(currentFormula.elements - condition)

                    //create an implication of the newFormula and the original formula
                    val implication = Implication(newFormula, currentFormula)

                    // Does the new formula imply the original formula?
                    solver.sat(implication, implication.variables) match {
                        case Sat(_) =>
                            // if sat, the condition is redundant, delete it, add it to deleted list
//                            println("this formula: " + newFormula + "  impliceert: " + currentFormula)
                            currentFormula = newFormula
                            toDeleteCond = condition :: toDeleteCond

                        case Unsat =>
                        // if unsat, don't delete, check next condition
                        case Unknown =>
                        // if unknown, to play it 'safe' same as unsat
                    }
                }
            }
//            println("This is todeleteCond: " + toDeleteCond)
            toDelete1 = toDelete1.updatedWith(schemeExp) {
                case Some(existingValue) => Some(existingValue ::: toDeleteCond)
                case None => Some(toDeleteCond)
            }
        }

        println("This is toDelete before filtering: " + toDelete1)

        //remove duplicates
        for ((schemeExp1, conditions) <- toDelete1){
            val cleanFormula = conditions.distinct
            toDelete1 = toDelete1.updated(schemeExp1, cleanFormula)
        }

        println("This is toDelete after filtering1: " + toDelete1)

        for ((schemeExp1, conditions) <- toDelete1) {
            var filteredConditions: List[Formula] = conditions
            for((schemeExp2, conditions2) <- toDelete1){
                if schemeExp1 != schemeExp2 then
                    filteredConditions = filteredConditions.filterNot {
                        case Assertion(SchemeFuncall(SchemeVar(Identifier("true?", idn1)), expr, idn2)) =>
                            conditions2.exists {
                                case Assertion(SchemeFuncall(SchemeVar(Identifier("true?", idn3)), expr1, idn4)) =>
//                                    if idn2 == idn4 then println("This is true expr1: " + Assertion(SchemeFuncall(SchemeVar(Identifier("true?", idn1)), expr, idn2)) + "  This is true expr2: " + Assertion(SchemeFuncall(SchemeVar(Identifier("true?", idn3)), expr1, idn4)))
                                    idn2 == idn4
                                case _ => false
                            }
                        case Assertion(SchemeFuncall(SchemeVar(Identifier("false?", idn1)), expr, idn2)) =>
                            conditions2.exists {
                                case Assertion(SchemeFuncall(SchemeVar(Identifier("false?", idn3)), expr1, idn4)) =>
//                                    if idn2 == idn4 then println("This is false expr1: " + Assertion(SchemeFuncall(SchemeVar(Identifier("false?", idn1)), expr, idn2)) + "  This is false expr2: " + Assertion(SchemeFuncall(SchemeVar(Identifier("false?", idn3)), expr1, idn4)))
                                    idn2 == idn4
                                case _ => false
                            }
                        case _ => false
                    }
            }
            toDelete1 = toDelete1.updated(schemeExp1,filteredConditions)
        }

        toDelete1 = toDelete1.filterNot { case (_, formulas) => formulas.isEmpty }

        println("This is toDelete after filtering2: " + toDelete1)

        // remove all assertions to immediately have the schemeExp's
        var toDelete  = toDelete1.map {
            case (schemeExp, formulas) => schemeExp -> formulas.map {
                case Assertion(exp) =>
                    exp
                case other => ???
            }
        }

        //In eender welke padconditie nagaan of de opposit van wat er in toDelete staat ook bestaat

        for ((schemeExp1, formulas) <- analysis.pathConditions) {
            for (formula <- formulas) {
                val conjuncts = formula.splitConj
                for ((schemeExp2, conditions) <- toDelete){
                    val conditionsToDelete = conditions.filterNot({
                        case SchemeFuncall(SchemeVar(Identifier("true?", idn1)), expr, idn2) =>
                            conjuncts.exists {
                                case Assertion(SchemeFuncall(SchemeVar(Identifier("false?", idn3)), expr1, idn4)) =>
                                    idn2 == idn4
                                case _ => false
                            }
                        case SchemeFuncall(SchemeVar(Identifier("false?", idn1)), expr, idn2) =>
                            conjuncts.exists {
                                case Assertion(SchemeFuncall(SchemeVar(Identifier("true?", idn3)), expr1, idn4)) =>
                                    idn2 == idn4
                                case _ => false
                            }
                        case _ => false
                    })
                    toDelete = toDelete.updated(schemeExp2,conditionsToDelete)
                }
            }
        }

        toDelete = toDelete.filterNot { case (_, formulas) => formulas.isEmpty }
        println("This is toDelete after opposites: " + toDelete)

        def deleteFromAST(ast: SchemeExp, toDelete: Map[SchemeExp, List[SchemeExp]]): SchemeExp = {

            def deleteFromExp(exp: SchemeExp, toDelete: Map[SchemeExp, List[SchemeExp]]): SchemeExp = {
                exp match {

                    case SchemeAssert(assertion, idn) =>
                        SchemeAssert(deleteFromExp(assertion, toDelete), idn)

                    case SchemeDefineVariable(name, value, idn) =>
                        SchemeDefineVariable(name, deleteFromExp(value, toDelete), idn)

                    case SchemeLambda(name, args, body, ann, idn) =>
                        val newBody = body.map(deleteFromExp(_, toDelete))
                        SchemeLambda(name, args, newBody, ann, idn)

                    case SchemeBegin(exps, idn) =>
                        val newExps = exps.map(deleteFromExp(_, toDelete))
                        SchemeBegin(newExps, idn)

                    //hierin gebeurd ook schemeand en schemeor
                    case SchemeIf(cond, cons, alt, idn) =>
                        SchemeIf(deleteFromExp(cond, toDelete), deleteFromExp(cons, toDelete), deleteFromExp(alt, toDelete), idn)

                    case SchemeSet(variable, value, idn) =>
                        SchemeSet(variable, deleteFromExp(value, toDelete), idn)

                    //recursivly call 'deletefromexp' on the bindings to update the bindings
                    //then recursivly call on the body to also update the body
                    case SchemeLet(bindings, body, idn) =>
                        val newBindings = bindings.map { case (v, e) => (v, deleteFromExp(e, toDelete)) }
                        val newBody = body.map(deleteFromExp(_, toDelete)) // body is een lijst van schemeexp
                        SchemeLet(newBindings, newBody, idn)

                    case SchemeLetStar(bindings, body, idn) =>
                        val newBindings = bindings.map { case (v, e) => (v, deleteFromExp(e, toDelete)) }
                        val newBody = body.map(deleteFromExp(_, toDelete)) // body is een lijst van schemeexp
                        SchemeLetStar(newBindings, newBody, idn)

                    case SchemeLetrec(bindings, body, idn) =>
                        val newBindings = bindings.map { case (v, e) => (v, deleteFromExp(e, toDelete)) }
                        val newBody = body.map(deleteFromExp(_, toDelete))
                        SchemeLetrec(newBindings, newBody, idn)

                    // inner-case om  voor > , < , = te matchen
                    case SchemeFuncall(f, args, idn) =>
                        //Ik check enkel of het true of false is ik ga niet na of het '> , <, =' is
                        //want ik hoef eigenlijk niet te weten wat de conditie is&
                        var newCond: SchemeExp = SchemeValue(Value.Nil, NoCodeIdentity)
                        for ((schemeExp, conditions) <- toDelete) {
                            //                            if idn == schemeExp.idn then
                            //                                println("this is the exp: " + schemeExp)
                            for (cond <- conditions) {
                                cond match {
                                    case SchemeFuncall(SchemeVar(Identifier(bool, idn1)), _, idn2) =>
//                                       println(idn)
//                                       println(idn1)
//                                       println(idn2)
                                        if (idn == idn2) then
                                            if (bool == "true?") then newCond = SchemeValue(Value.Boolean(true), NoCodeIdentity)
                                            else if (bool == "false?") then newCond = SchemeValue(Value.Boolean(false), NoCodeIdentity)
                                            else SchemeFuncall(SchemeVar(Identifier(bool, idn1)), _, idn2)
                                        else SchemeFuncall(SchemeVar(Identifier(bool, idn1)), _, idn2)
                                    case _ => ???
                                }
                            }
                        }
                        val res: SchemeExp = if newCond != SchemeValue(Value.Nil, NoCodeIdentity) then newCond else SchemeFuncall(f, args, idn)
                        res

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

                    case _ => exp
                }
            }
            println("This is the old AST : \n")
            print(ast.prettyString() + "\n")
            val newAST = deleteFromExp(ast, toDelete)
            println("Old Ast equal to new AST?: " + ast.eql(newAST))
            newAST
        }

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

        val newAST = deleteFromAST(exp, toDelete)

        //AST weer omvormen naar Scheme Code
        println("This is the new AST: \n")
        print(newAST.prettyString() + "\n")

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

    repl()

