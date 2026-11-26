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

/-- Remaining budget for an expression serialized as a tree. Repeated subexpressions
count each time they occur in a statement. -/
private partial def remainingStatementNodes (e : Expr) (budget : Nat) : Nat :=
  if budget = 0 then 0 else
    let next := budget - 1
    match e with
    | .app f a => remainingStatementNodes a (remainingStatementNodes f next)
    | .lam _ t b _ | .forallE _ t b _ =>
        remainingStatementNodes b (remainingStatementNodes t next)
    | .letE _ t v b _ =>
        remainingStatementNodes b (remainingStatementNodes v (remainingStatementNodes t next))
    | .mdata _ b | .proj _ _ b => remainingStatementNodes b next
    | _ => next

/-- Count references to each expression, in dependency order. -/
private partial def statementReferences (e : Expr) :
    StateM (Std.HashMap ExprStructEq Nat × Array Expr) Unit := do
  let (counts, order) ← get
  if let some n := counts[(e : ExprStructEq)]? then
    set (counts.insert e (n + 1), order)
  else
    set (counts.insert e 1, order)
    e.foldlM (fun () child => statementReferences child) ()
    modify fun (counts, order) => (counts, order.push e)

private meta def shareStatement (type : Expr) : MetaM Expr := do
  let (_, (counts, order)) := (statementReferences type).run ({}, #[])
  let shared := order.filter fun (e : Expr) =>
    !e.hasLooseBVars && counts[ExprStructEq.mk e]! > 1 && remainingStatementNodes e 128 == 0
  bindShared shared.toList {}
where
  bindShared (terms : List Expr) (refs : Std.HashMap ExprStructEq Expr) : MetaM Expr :=
    match terms with
    | [] => pure (type.replace fun e => refs[(e : ExprStructEq)]?)
    | e :: rest => do
        let value := e.replace fun child => refs[(child : ExprStructEq)]?
        mapLetDecl `shared (← inferType value) value fun ref =>
          bindShared rest (refs.insert e ref)

-- The compiled evaluator proposes data. The kernel checks the resulting equality.
private meta def stageQuoted (α : Type) (type : Expr) (quoteValue : α → MetaM Expr)
    (limitStatementSize : Bool) (shareLargeStatement : Bool := false) : Simproc := fun e => do
  if e.hasFVar || e.hasMVar || e.hasLooseBVars then
    return .rfl
  let (output, equality) ← liftM (m := MetaM) <| do
    let value ← unsafe evalExpr α type e
    let output ← quoteValue value
    let theoremType ← mkEq e output
    let proof ← mkEqRefl output
    -- Keep large computations in the proof term, where their expressions
    -- need not be serialized as exported theorem statements.
    if e.isAppOfArity ``Model.ofRat 1 || e.isAppOfArity ``Model.widen 2 ||
        (limitStatementSize && remainingStatementNodes theoremType 262144 == 0) then
      return (output, mkExpectedPropHint proof theoremType)
    let auxType ←
      if shareLargeStatement && remainingStatementNodes theoremType 262144 == 0 then
        shareStatement theoremType
      else pure theoremType
    let equality ← try
      withOptions (fun opts ↦ Lean.maxHeartbeats.set (Elab.async.set opts false) 350000) <|
        mkAuxLemma [] auxType proof
    catch err =>
      throwError "kernel replay of {e.getAppFn} failed: {err.toMessageData}"
    pure (output, mkConst equality)
  return .step (← Sym.shareCommon output) equality (done := true)

meta def stageLiteral (α : Type) [ToExpr α] (limitStatementSize : Bool := false) : Simproc :=
  stageQuoted α (toTypeExpr (α := α)) (pure ∘ toExpr) limitStatementSize

meta def stageSharedLiteral (α : Type) [ToExpr α] : Simproc :=
  stageQuoted α (toTypeExpr (α := α)) (pure ∘ toExpr) false (shareLargeStatement := true)

meta def stageModel (limitStatementSize : Bool := false) : Simproc :=
  stageQuoted Model (mkConst ``Model) quoteModel limitStatementSize

meta def stageOnModels (count : Nat) (proc : Simproc) : Simproc := fun e => do
  unless (e.getAppArgs.extract 0 count).all (fun a => a.isAppOfArity ``Model.mk 2) do
    throwError "expected reduced model inputs for {e.getAppFn}"
  proc e

end RefinedBMV.PositiveCenter.CompactTaylorModel.Replay
