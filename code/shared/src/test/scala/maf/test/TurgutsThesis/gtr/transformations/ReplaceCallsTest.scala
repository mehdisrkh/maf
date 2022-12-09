package maf.test.TurgutsThesis.gtr.transformations

import maf.TurgutsThesis.gtr.transformations.ReplaceCalls
import maf.language.scheme.{SchemeBegin, SchemeParser}

class ReplaceCallsTest extends AnyFlatSpecTransformations:
  "ReplaceCalls" should "replace the calls to define-bound lambda" in {
    val programText: String =
      """(begin
        |  (define (f x) (* x x))
        |  (f 1)
        |  (+ 2 2)
        |  (f 111))
        |  """.stripMargin

    val t: SchemeBegin = SchemeParser.parseProgramText(programText).last.asInstanceOf[SchemeBegin]
    val defineExp = t.exps.head

    suggestedTrees = ReplaceCalls.transform(t, defineExp) //should remove calls to f

    assert(suggestedTrees.length > 1)
    suggestedTrees.foreach(s => println(s.prettyString()))
    assertTreeString("(begin #f (+ 2 2) #f)")
    assertTreeString("(begin 1 (+ 2 2) 1)")
    assertTreeString("(begin 'S (+ 2 2) 'S)")
  }

  "ReplaceCalls" should "remove the calls to let-bound lambda" in {
    val programText: String =
      """(begin
        |  (let ((f (lambda (x) (* x x))))
        |    (f 10)
        |    (f 100)
        |    1000)
        |  (+ 2 2))
        |  """.stripMargin

    val t: SchemeBegin = SchemeParser.parseProgramText(programText).last.asInstanceOf[SchemeBegin]
    val letExp = t.exps.head

    suggestedTrees = ReplaceCalls.transform(t, letExp) //should remove calls to f
    assert(suggestedTrees.length > 1)
    assertTreeString("(begin (let () #t #t 1000) (+ 2 2))")
    assertTreeString("(begin (let () 1 1 1000) (+ 2 2))")
    assertTreeString("(begin (let () 'S 'S 1000) (+ 2 2))")
  }

  "ReplaceCalls" should "return an empty list given a non-lambda-binding exp" in {
    val programText: String =
      """(begin
        |  (let ((f 100))
        |    (+ f f)
        |    1000)
        |  (+ 2 2))
        |  """.stripMargin

    val t: SchemeBegin = SchemeParser.parseProgramText(programText).last.asInstanceOf[SchemeBegin]
    val letExp = t.exps.head

    suggestedTrees = ReplaceCalls.transform(t, letExp)
    assert(suggestedTrees equals List())
  }