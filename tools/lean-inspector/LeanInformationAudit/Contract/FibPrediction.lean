import LeanInformationAudit.Contract.FibSource

namespace LeanInformationAudit.FibPrediction
open Lean CompiledSourceScope FibSource

private def unknown (reason : String) : Json := Json.mkObj [
  ("kind", toJson "unknown"), ("reason", toJson reason)]

private def label (base : Name) (names : List String) (term : Expr) : M String := do
  let term ← constructorHead term
  for name in names do
    if term.isConstOf (base.str name) then return name
  fail "fib.prediction_literal_tag"

private partial def letters (term : Expr) (depth : Nat := 0) : M Json := do
  debit
  if depth > 256 then fail "fib.prediction_word_limit"
  let term ← constructorHead term
  if term.isAppOfArity ``List.nil 1 then return toJson ([] : List String)
  unless term.isAppOfArity ``List.cons 3 do fail "fib.prediction_literal_word"
  let head ← label `D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd.Window
    ["zero", "low", "high", "ends", "middle"] term.getAppArgs[1]!
  let tail ← letters term.getAppArgs[2]! (depth + 1)
  let tail ← IO.ofExcept tail.getArr?
  return Json.arr (#[toJson head] ++ tail)

private def point (term : Expr) : M Json := do
  let term ← constructorHead term
  let base := `LeanInformationAudit.AuricFib.NativePrediction.Point
  if term.isConstOf (base ++ `rejected) then
    return Json.mkObj [("kind", toJson "rejected")]
  let fields ← fields (base ++ `live) term
  let seam ← IO.ofExcept (Contract.Literal.bool "fib.prediction_seam" (← constructorHead fields[0]!))
  let left ← IO.ofExcept (Contract.Literal.nat "fib.prediction_coordinate" (← constructorHead fields[1]!))
  let right ← IO.ofExcept (Contract.Literal.nat "fib.prediction_coordinate" (← constructorHead fields[2]!))
  return Json.mkObj [("kind", toJson "live"), ("seam", toJson seam),
    ("composition", toJson [left, right])]

/-- Only this compiled producer projects a certificate. The public arithmetic
analyzer never promotes a supplied JSON claim to compiled evidence. -/
def extract (occurrence : Expr) (info : ConstantInfo) (optional : Expr) : M Json := do
  try
    let optional ← constructorHead optional
    if optional.isAppOfArity ``Option.none 1 then
      return unknown "no source-owned operation contract supplied"
    unless optional.isAppOfArity ``Option.some 2 do fail "fib.prediction_optional_contract"
    let prediction := optional.getAppArgs[1]!
    indexed `LeanInformationAudit.AuricFib.Contract.Prediction prediction occurrence
    let parts ← fields `LeanInformationAudit.AuricFib.Contract.Prediction.mk prediction
    bindNative occurrence info parts[0]!
    let contract ← fields `LeanInformationAudit.AuricFib.NativePrediction.Contract.mk parts[1]!
    let summary ← label `LeanInformationAudit.AuricFib.NativePrediction.Summary
      ["reply", "seamReply", "memory"] contract[0]!
    let actions ← letters contract[1]!
    let evidence ← constructorHead contract[2]!
    let tag := evidence.getAppFn.constName?.getD .anonymous
    let base := `LeanInformationAudit.AuricFib.NativePrediction.Evidence
    let proofFields ← fields tag evidence
    let mut result := [("summary", toJson summary), ("actions", actions),
      ("scope", toJson "native rawMachine(0); complete integer evaluator states; includes all natural source histories"),
      ("state_finiteness", toJson "no finite state presentation or pair rate acquired"),
      ("source", describe parts[0]!),
      ("operation", toJson "rawTransition; total; absorbing rejection retained"),
      ("task", toJson "rawOutput after the selected continuation; Option integer"),
      ("limits", toJson ["no multiwindow source probability law acquired",
        "no physical or coherent instrument certified", "no convergence claim"])]
    if tag == base ++ `unknown then
      let reason ← IO.ofExcept (Contract.Literal.string "fib.prediction_reason" (← constructorHead proofFields[0]!))
      result := result ++ [("kind", toJson "unknown"), ("reason", toJson reason)]
    else if tag == base ++ `closed then
      result := result ++ [("kind", toJson "available"), ("claim", toJson "closed"),
        ("word_scope", toJson "every finite word over declared native letters"),
        ("certificate", describe (← projectType proofFields[0]!)),
        ("proof", describe proofFields[0]!)]
    else if tag == base ++ `separated then
      let witness ← fields `LeanInformationAudit.AuricFib.NativePrediction.Separation.mk proofFields[0]!
      result := result ++ [("kind", toJson "available"), ("claim", toJson "separated"),
        ("word_scope", toJson "the supplied permitted word; no exhaustive search claim"),
        ("witness", Json.mkObj [("left", ← point witness[0]!), ("right", ← point witness[1]!),
          ("word", ← letters witness[2]!),
          ("permitted", describe (← projectType witness[3]!)),
          ("same_summary", describe (← projectType witness[4]!)),
          ("different_reply", describe (← projectType witness[5]!))]),
        ("proof", describe proofFields[0]!)]
    else fail "fib.prediction_evidence_constructor"
    return Json.mkObj result
  catch error => return unknown s!"operation evidence unavailable: {error}"

end LeanInformationAudit.FibPrediction
