/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/GeometricCertificate/CachedVerification
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Reuse kernel-checked arithmetic across adjacent leaves of the left strip. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.GeometricCertificate.Verification

/-! Reuse exact arithmetic reductions across leaves of the left-strip certificate. -/

namespace RefinedBMV.PositiveCenter.LocalTaylor

open Lean Elab Tactic
open Lean.Meta hiding check
open private band check checkCover from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.LeftStripGeometricCertificate
open private Expression Expression.value Expression.unary Expression.binary Expression.eval
  eval_scalar eval_unary eval_binary quoteChecked from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.GeometricCertificate.Verification

/-- Closed arithmetic applications on quoted inputs can recur in different leaves. -/
private unsafe def evalCached (arithmetic : IO.Ref (Std.HashMap Expr (Expr × Expr)))
    (root : Expr) : MetaM (Expr × Expr) := do
  let expressions ← IO.mkRef ({} : Std.HashMap Expr (Expr × Expr))
  let compute (application : Expr) : MetaM (Expr × Expr) := do
    if let some cached := (← arithmetic.get)[application]? then
      return cached
    let result ← quoteChecked application
    arithmetic.modify (·.insert application result)
    return result
  let rec prove (fuel : Nat) (expression : Expr) : MetaM (Expr × Expr) := do
    let fuel+1 := fuel | throwError "arithmetic expression is too deep"
    if let some cached := (← expressions.get)[expression]? then
      return cached
    let reduced ← withTransparency .all <| whnf expression
    let result ← match_expr reduced with
      | Expression.value input => quoteChecked input
      | Expression.unary op arg => do
        let (value, h) ← prove fuel arg
        let (output, hOp) ← compute (mkApp op value)
        pure (output, mkAppN (mkConst ``eval_unary) #[op, arg, value, output, h, hOp])
      | Expression.binary op left right => do
        let (a, ha) ← prove fuel left
        let (b, hb) ← prove fuel right
        let (output, hOp) ← compute (mkApp2 op a b)
        pure (output, mkAppN (mkConst ``eval_binary) #[op, left, right, a, b, output, ha, hb, hOp])
      | _ => throwError "expected an arithmetic expression constructor"
    expressions.modify (·.insert expression result)
    return result
  prove 160 root

private unsafe def checkCachedLeaf
    (arithmetic : IO.Ref (Std.HashMap Expr (Expr × Expr))) : TacticM Unit := do
  evalTactic (← `(tactic| (apply coverLeaf; unfold check; rw [← eval_scalar])))
  let goal ← getMainGoal
  goal.withContext do
    let target ← goal.getType
    let some application := target.find? (·.isAppOfArity ``Expression.eval 1) |
      throwError "expected expression evaluation"
    let (output, proof) ← withFreshCache <| evalCached arithmetic application.appArg!
    let proof := mkExpectedPropHint proof (← mkEq application output)
    let rewrite ← goal.rewrite target proof
    let goal ← goal.replaceTargetEq rewrite.eNew rewrite.eqProof
    replaceMainGoal (goal :: rewrite.mvarIds)
  evalTactic (← `(tactic| decide +kernel))

syntax (name := verifyCachedCover) "verify_left_strip_cover_cached " "[" str,* "]" : tactic

/-- Check the designated leaf paths using one arithmetic cache for the entire cover. -/
@[tactic verifyCachedCover] private unsafe def elabVerifyCachedCover : Tactic := fun stx => do
  let `(tactic| verify_left_strip_cover_cached [$paths:str,*]) := stx |
    throwUnsupportedSyntax
  let paths := paths.getElems.toList.map fun path => path.getString.toList
  let arithmetic ← IO.mkRef ({} : Std.HashMap Expr (Expr × Expr))
  let rec prove (fuel : Nat) (paths : List (List Char)) : TacticM Unit := focus do
    if paths.contains [] then
      checkCachedLeaf arithmetic
    else
      let fuel+1 := fuel | throwError "missing leaf in the left-strip cover"
      let children (bit : Char) := paths.filterMap fun
        | first :: rest => if first == bit then some rest else none
        | [] => none
      evalTactic (← `(tactic| apply coverSplit))
      prove fuel (children '0')
      prove fuel (children '1')
  prove (paths.foldl (fun length path => max length path.length) 0) paths

end RefinedBMV.PositiveCenter.LocalTaylor
