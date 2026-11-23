import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.LeftStripGeometricCertificate
import Lean.Meta.Tactic.Cbv

/-! # Exact finite positivity verification for the geometric left strip -/

namespace RefinedBMV.PositiveCenter.LocalTaylor
open private check checkCover splitBox band Box from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.LeftStripGeometricCertificate

open RefinedBMV.PositiveCenter.SmallCorner
open Lean in
private def intervalValue (q : RoundedInterval) : Expr :=
  mkApp (mkConst ``RoundedInterval.mk) (toExpr q.endpoints)

open private Model from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.LeftStripGeometricCertificate

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
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.LeftStripGeometricCertificate

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
  let thm ← withOptions (Lean.Elab.async.set · false) <| mkAuxLemma [] theoremType proof
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


private theorem coverLeaf {n : ℕ} {B : Box} (h : check B = true) :
    checkCover n B = true := by
  cases n <;> simp only [checkCover, h, Bool.true_or]

private theorem coverSplit {n : ℕ} {B : Box}
    (h₁ : checkCover n (splitBox B).1 = true)
    (h₂ : checkCover n (splitBox B).2 = true) :
    checkCover (n+1) B = true := by
  simp only [checkCover, h₁, h₂, Bool.and_true, Bool.or_true]

open Lean Elab Tactic in
private def verifyCover (paths : List (List Char)) : TacticM Unit := do
  let rec prove (depth : Nat) (paths : List (List Char)) : TacticM Unit := do
    if paths == [[]] then
      evalTactic (← `(tactic|
        (apply coverLeaf
         unfold check
         rw [← eval_scalar]
         check_expression
         decide +kernel)))
    else
      let depth+1 := depth | throwError "cover paths exceed the certified subdivision depth"
      let left := paths.filterMap fun
        | '0' :: path => some path
        | _ => none
      let right := paths.filterMap fun
        | '1' :: path => some path
        | _ => none
      unless !left.isEmpty && !right.isEmpty && left.length + right.length = paths.length do
        throwError "invalid binary subdivision"
      evalTactic (← `(tactic| apply coverSplit))
      let [g₁, g₂] ← getGoals | throwError "expected two cover subgoals"
      setGoals [g₁]
      prove depth left
      setGoals [g₂]
      prove depth right
  prove 5 paths

open Lean Elab Tactic in
elab "verify_cover " paths:str : tactic =>
  verifyCover ((paths.getString.splitOn " ").map String.toList)

-- Each successful leaf is checked with the centered enclosure arithmetic.
set_option maxRecDepth 12000 in
set_option maxHeartbeats 40000000 in
private theorem band1 : checkCover 5 (band 1 (5/4)) = true := by
  verify_cover "00000 00001 0001 00100 00101 0011 01000 01001 0101 01100 01101 0111 10000 10001 10010 10011 10100 10101 10110 10111 11000 11001 1101 11100 11101 1111"

-- Each successful leaf is checked with the centered enclosure arithmetic.
set_option maxRecDepth 12000 in
set_option maxHeartbeats 40000000 in
private theorem band2 : checkCover 5 (band (5/4) (3/2)) = true := by
  verify_cover "0000 0001 0010 0011 0100 0101 0110 0111 1000 1001 1010 1011 1100 1101 1110 1111"

-- Each successful leaf is checked with the centered enclosure arithmetic.
set_option maxRecDepth 12000 in
set_option maxHeartbeats 40000000 in
private theorem band3 : checkCover 5 (band (3/2) 2) = true := by
  verify_cover "00000 00001 00010 00011 00100 00101 00110 00111 01000 01001 01010 01011 0110 01110 01111 10000 10001 10010 10011 10100 10101 10110 10111 11000 11001 11010 11011 11100 11101 11110 11111"

-- Each successful leaf is checked with the centered enclosure arithmetic.
set_option maxRecDepth 12000 in
set_option maxHeartbeats 40000000 in
private theorem band4 : checkCover 5 (band 2 (5/2)) = true := by
  verify_cover "00000 00001 00010 00011 0010 0011 0100 01010 01011 0110 01110 01111 10000 10001 10010 10011 10100 10101 10110 10111 11000 11001 11010 11011 11100 11101 11110 11111"

-- Each successful leaf is checked with the centered enclosure arithmetic.
set_option maxRecDepth 12000 in
set_option maxHeartbeats 40000000 in
private theorem band5 : checkCover 5 (band (5/2) 3) = true := by
  verify_cover "0000 00010 00011 00100 00101 00110 00111 01000 01001 01010 01011 01100 01101 01110 01111 10000 10001 10010 10011 10100 10101 10110 10111 11000 11001 11010 11011 11100 11101 11110 11111"

-- Each successful leaf is checked with the centered enclosure arithmetic.
set_option maxRecDepth 12000 in
set_option maxHeartbeats 40000000 in
private theorem band6 : checkCover 5 (band 3 (7/2)) = true := by
  verify_cover "00000 00001 00010 00011 00100 00101 00110 00111 01000 01001 01010 01011 01100 01101 01110 01111 10000 10001 10010 10011 10100 10101 10110 10111 11000 11001 11010 11011 11100 11101 11110 11111"

private theorem moderateLeftStripCheck_verified : moderateLeftStripCheck 5 = true := by
  simp only [moderateLeftStripCheck, band1, band2, band3, band4, band5, band6, Bool.and_true]

end RefinedBMV.PositiveCenter.LocalTaylor

namespace RefinedBMV.PositiveCenter

/-- The original mixed logarithmic kernel derivative is strictly negative in the
left strip with gap at least one. -/
theorem leftStrip_logKernel_mixed_lt_ge_one {p : ℕ} (hp : 11 ≤ p) {u v : ℝ}
    (hu : 0 < u) (humax : u ≤ 1 / 2) (hd : 1 ≤ v - u) :
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < 0 :=
  leftStrip_logKernel_mixed_lt_of_certificate LocalTaylor.moderateLeftStripCheck_verified
    hp hu humax hd

/-- info: 'RefinedBMV.PositiveCenter.leftStrip_logKernel_mixed_lt_ge_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms leftStrip_logKernel_mixed_lt_ge_one

end RefinedBMV.PositiveCenter
