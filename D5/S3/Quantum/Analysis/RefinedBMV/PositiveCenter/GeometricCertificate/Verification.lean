/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/GeometricCertificate/Verification
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact kernel verification infrastructure for the left geometric strip. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.LeftStripGeometricCertificate

/-! # Exact finite positivity verification for the geometric left strip -/

namespace RefinedBMV.PositiveCenter.LocalTaylor
open private check checkCover splitBox Box from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.LeftStripGeometricCertificate

open RefinedBMV.PositiveCenter.SmallCorner
open Lean in
private def intervalValue (q : RoundedInterval) : Expr :=
  mkApp (mkConst ``RoundedInterval.mk) (toExpr q.endpoints)

open private Model from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.LeftStripGeometricModels

open Lean Meta in
private def quoteModel (P : Model) : MetaM Expr := do
  let ty := mkApp2 (mkConst ``Prod [.zero, .zero]) (toTypeExpr (α := ℕ × ℕ × ℕ))
    (mkConst ``RoundedInterval)
  let es ← P.mapM fun (k, c) => do
    mkAppM ``Prod.mk #[toExpr k, intervalValue c]
  mkListLit ty es

open private Arithmetic Arithmetic.mk Arithmetic.scalar Arithmetic.num Arithmetic.add
  Arithmetic.sub Arithmetic.mul Arithmetic.exp Arithmetic.phi Arithmetic.root Arithmetic.defect
  Arithmetic.inverse modelArithmetic from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.LeftStripGeometricModels

private inductive Expression where
  | value (v : Option Model)
  | unary (op : Option Model → Option Model) (a : Expression)
  | binary (op : Option Model → Option Model → Option Model) (a b : Expression)

private def Expression.eval : Expression → Option Model
  | .value v => v
  | .unary op a => op a.eval
  | .binary op a b => op a.eval b.eval

private def expressionArithmetic : Arithmetic Expression :=
  let o := modelArithmetic
  Arithmetic.mk (Expression.value ∘ Arithmetic.num o)
    (Expression.binary (Arithmetic.add o)) (Expression.binary (Arithmetic.sub o))
    (Expression.binary (Arithmetic.mul o)) (Expression.unary (Arithmetic.exp o))
    (Expression.unary (Arithmetic.phi o)) (Expression.unary (Arithmetic.root o))
    (Expression.binary (Arithmetic.defect o)) (Expression.unary (Arithmetic.inverse o))

private theorem eval_scalar (h a d : Option Model) :
    (Arithmetic.scalar expressionArithmetic (.value h) (.value a) (.value d)).eval =
      Arithmetic.scalar modelArithmetic h a d := by
  rfl

private theorem eval_unary {f : Option Model → Option Model} {e : Expression}
    {v w : Option Model} (he : e.eval = v) (hw : f v = w) :
    (Expression.unary f e).eval = w :=
  (congrArg f he).trans hw

private theorem eval_binary {f : Option Model → Option Model → Option Model}
    {e₁ e₂ : Expression} {v₁ v₂ w : Option Model}
    (h₁ : e₁.eval = v₁) (h₂ : e₂.eval = v₂) (hw : f v₁ v₂ = w) :
    (Expression.binary f e₁ e₂).eval = w :=
  (congrArg₂ f h₁ h₂).trans hw

open Lean Meta in
private unsafe def quoteChecked (e : Expr) : MetaM (Expr × Expr) := do
  let ty := mkApp (mkConst ``Option [.zero]) (mkConst ``Model)
  let val ← evalExpr (Option Model) ty e
  let output ← match val with
    | none => pure (mkApp (mkConst ``Option.none [.zero]) (mkConst ``Model))
    | some p => pure (mkApp2 (mkConst ``Option.some [.zero]) (mkConst ``Model) (← quoteModel p))
  let proof ← mkEqRefl output
  let theoremType ← mkEq e output
  let thm ← withOptions
      (fun opts => Lean.maxHeartbeats.set (Lean.Elab.async.set opts false) 350000) <|
    mkAuxLemma [] theoremType proof
  return (output, mkConst thm)

open Lean Meta in
private unsafe def evalChecked (root : Expr) : MetaM (Expr × Expr) := do
  let memo ← IO.mkRef ({} : Std.HashMap Expr (Expr × Expr))
  let rec prove (fuel : Nat) (e : Expr) : MetaM (Expr × Expr) := do
    let fuel+1 := fuel | throwError "arithmetic expression is too deep"
    if let some cached := (← memo.get)[e]? then return cached
    let expr ← withTransparency .all <| whnf e
    let result ← match_expr expr with
      | Expression.value v => quoteChecked v
      | Expression.unary f a => do
        let (va, ha) ← prove fuel a
        let (v, hv) ← quoteChecked (mkApp f va)
        let proof := mkAppN (mkConst ``eval_unary) #[f, a, va, v, ha, hv]
        pure (v, proof)
      | Expression.binary f a b => do
        let (va, ha) ← prove fuel a
        let (vb, hb) ← prove fuel b
        let (v, hv) ← quoteChecked (mkApp2 f va vb)
        let proof := mkAppN (mkConst ``eval_binary) #[f, a, b, va, vb, v, ha, hb, hv]
        pure (v, proof)
      | _ => throwError "expected an arithmetic expression constructor"
    memo.modify (·.insert e result)
    return result
  prove 160 root

syntax (name := checkExpression) "check_expression" : tactic

open Lean Elab Tactic Meta in
@[tactic checkExpression] unsafe def elabCheckExpression : Tactic := fun _ => do
  let g ← getMainGoal
  g.withContext do
    let t ← g.getType
    let some app := t.find? (·.isAppOfArity ``Expression.eval 1) |
      throwError "expected expression evaluation"
    let (v, proof) ← withFreshCache <| evalChecked app.appArg!
    let proof := mkExpectedPropHint proof (← mkEq app v)
    let rw ← g.rewrite t proof
    let g ← g.replaceTargetEq rw.eNew rw.eqProof
    replaceMainGoal (g :: rw.mvarIds)


theorem coverLeaf {n : ℕ} {B : Box} (h : check B = true) :
    checkCover n B = true := by
  cases n <;> simp only [checkCover, h, Bool.true_or]

theorem coverSplit {n : ℕ} {B : Box}
    (h₁ : checkCover n (splitBox B).1 = true)
    (h₂ : checkCover n (splitBox B).2 = true) :
    checkCover (n+1) B = true := by
  simp only [checkCover, h₁, h₂, Bool.and_true, Bool.or_true]

open Lean in
macro "left_strip_box " b:term:max p:str : term => do
  let mut box := b
  for bit in p.getString.toList do
    box ← match bit with
    | '0' => `(term| (splitBox $box).1)
    | '1' => `(term| (splitBox $box).2)
    | _ => Macro.throwError "left-strip box paths contain only 0 and 1"
  return box

macro "verify_left_strip_leaf" : tactic =>
  `(tactic|
    (unfold check
     rw [← eval_scalar]
     check_expression
     decide +kernel))

end RefinedBMV.PositiveCenter.LocalTaylor
