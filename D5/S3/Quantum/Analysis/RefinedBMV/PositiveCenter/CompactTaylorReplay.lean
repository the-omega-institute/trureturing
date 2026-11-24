/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactTaylorReplay
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Kernel checking of intermediate rational Taylor models. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactTaylorModel
import Lean.Elab.Tactic.CbvSimproc
import Lean.Meta.Eval

/-! Kernel replay of intermediate model equalities. -/

namespace RefinedBMV.PositiveCenter.CompactTaylorModel.Replay

open Lean Meta Sym.Simp
open DimThree.Certificate (Sparse Term)

private meta def quoteModel (p : Model) : MetaM Expr := do
  let terms ← p.polynomial.terms.mapM fun a => do
    let (i, j, k) := a.exponents
    let jk ← mkAppM ``Prod.mk #[toExpr j, toExpr k]
    let ijk ← mkAppM ``Prod.mk #[toExpr i, jk]
    return mkApp2 (mkConst ``DimThree.Certificate.Term.mk) ijk (toExpr a.coefficient)
  let terms ← mkListLit (mkConst ``DimThree.Certificate.Term) terms
  return mkApp2 (mkConst ``Model.mk) (mkApp (mkConst ``Sparse.mk) terms) (toExpr p.radius)

-- The compiled evaluator proposes only data. Each equality is checked in a separate theorem.
private meta def stageQuoted (α : Type) (type : Expr) (quoteValue : α → MetaM Expr) :
    Simproc := fun e => do
  if e.hasFVar || e.hasMVar || e.hasLooseBVars then
    return .rfl
  let (output, equality) ← liftM (m := MetaM) <| do
    let value ← unsafe evalExpr α type e
    let output ← quoteValue value
    let theoremType ← mkEq e output
    let proof ← mkEqRefl output
    let equality ← try
      withOptions (fun opts ↦ Lean.maxHeartbeats.set (Elab.async.set opts false) 350000) <|
        mkAuxLemma [] theoremType proof
    catch err =>
      throwError "kernel replay of {e.getAppFn} failed: {err.toMessageData}"
    pure (output, equality)
  return .step (← Sym.shareCommon output) (mkConst equality) (done := true)

meta def stageLiteral (α : Type) [ToExpr α] : Simproc :=
  stageQuoted α (toTypeExpr (α := α)) (pure ∘ toExpr)

meta def stageModel : Simproc := stageQuoted Model (mkConst ``Model) quoteModel

meta def stageOnModels (count : Nat) (proc : Simproc) : Simproc := fun e => do
  unless (e.getAppArgs.extract 0 count).all (fun a => a.isAppOfArity ``Model.mk 2) do
    throwError "expected reduced model inputs for {e.getAppFn}"
  proc e

end RefinedBMV.PositiveCenter.CompactTaylorModel.Replay
