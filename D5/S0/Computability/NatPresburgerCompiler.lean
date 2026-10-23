/- GID: D5/S0/Computability/NatPresburgerCompiler
   generality: G
   mirror-B: D5/B/S0/Computability/NatPresburgerCompiler
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native Nat terms and every guarded binder preserve exact integer semantics. -/

import D5.S0.Computability.NatPresburgerEnvironment
import Mathlib.ModelTheory.Arithmetic.Presburger.Basic

namespace NatPresburger

open FirstOrder Language PresburgerArithmetic

def compileTerm {m n : Nat} : presburger.Term (Fin m ⊕ Fin n) → Affine
  | .var i => basis (position i)
  | .func .zero _ => .const 0
  | .func .one _ => .const 1
  | .func .add ts => (compileTerm (ts 0)).add (compileTerm (ts 1))

theorem compile_term_correct {m n : Nat} (t : presburger.Term (Fin m ⊕ Fin n))
    (v : Fin m → Nat) (xs : Fin n → Nat) :
    (compileTerm t).eval (environment v xs) =
      Int.ofNat (t.realize (Sum.elim v xs)) := by
  induction t with
  | var i => exact (eval_basis _ _).trans (environment_lookup v xs i)
  | func f ts ih =>
    cases f with
    | zero => simp [compileTerm, Term.realize, presburger.funMap_zero]
    | one => simp [compileTerm, Term.realize, presburger.funMap_one]
    | add => simp [compileTerm, Term.realize, presburger.funMap_add, ih]

private def equality (s t : Affine) : PresburgerArithmetic.Formula :=
  let d := s.add t.neg
  .qf (.and (.atom (.le d)) (.atom (.le d.neg)))

private def implication (p q : PresburgerArithmetic.Formula) :
    PresburgerArithmetic.Formula := .or (.not p) q

private def nonnegativeHead : PresburgerArithmetic.Formula :=
  .qf (.atom (.le (basis 0)))

/-- Each native universal binder is guarded at its own integer head coordinate. -/
def compile {m : Nat} : {n : Nat} → presburger.BoundedFormula (Fin m) n →
    PresburgerArithmetic.Formula
  | _, .falsum => .qf .falsity
  | _, .equal s t => equality (compileTerm s) (compileTerm t)
  | _, .rel r _ => nomatch r
  | _, .imp p q => implication (compile p) (compile q)
  | _, .all p => PresburgerArithmetic.Formula.all
      (implication nonnegativeHead (compile p))

private theorem equality_correct (s t : Affine) (env : List Int) :
    (equality s t).holds env ↔ s.eval env = t.eval env := by
  simp only [equality, PresburgerArithmetic.Formula.holds, QF.eval, Atom.eval,
    Bool.and_eq_true, decide_eq_true_eq, Affine.eval_neg, Affine.eval_add]
  omega

private theorem implication_correct (p q : PresburgerArithmetic.Formula)
    (env : List Int) :
    (implication p q).holds env ↔ (p.holds env → q.holds env) := by
  classical
  simp [implication, PresburgerArithmetic.Formula.holds, or_iff_not_imp_left]

/-- The full native semantics, including arbitrary nesting and alternation. -/
theorem compile_correct {m n : Nat} (φ : presburger.BoundedFormula (Fin m) n)
    (v : Fin m → Nat) (xs : Fin n → Nat) :
    (compile φ).holds (environment v xs) ↔ φ.Realize v xs := by
  induction φ with
  | falsum => simp [compile, PresburgerArithmetic.Formula.holds, QF.eval,
      BoundedFormula.Realize]
  | equal s t =>
    rw [compile, equality_correct, compile_term_correct, compile_term_correct]
    exact Int.ofNat_inj
  | rel r ts => nomatch r
  | imp p q ihp ihq =>
    rw [compile, implication_correct, ihp, ihq]
    rfl
  | all p ih =>
    classical
    simp only [compile, PresburgerArithmetic.Formula.all,
      PresburgerArithmetic.Formula.holds, not_exists, Classical.not_not,
      implication_correct, nonnegativeHead, QF.eval, Atom.eval, eval_basis,
      List.getElem?_cons_zero, Option.getD_some, decide_eq_true_eq]
    change (∀ z : Int, 0 ≤ z → (compile p).holds (z :: environment v xs)) ↔
      ∀ x : Nat, p.Realize v (Fin.snoc xs x)
    constructor
    · intro h x
      rw [← ih, environment_snoc]
      exact h x (Int.natCast_nonneg x)
    · intro h z hz
      have hcast : (z.toNat : Int) = z := Int.toNat_of_nonneg hz
      have hx := (ih (xs := Fin.snoc xs z.toNat)).mpr (h z.toNat)
      rw [environment_snoc, hcast] at hx
      exact hx

end NatPresburger
