/- GID: D5/S3/Geometry/AlgebraicBoundary/TauCeti/Algebra/Polynomial/Rolle
   generality: G
   mirror-B: D5/B/S3/Geometry/AlgebraicBoundary/TauCeti/Algebra/Polynomial/Rolle
   mirror-E: none(waiver:external-source-adaptation)
   anchors: []
   utility: none
   digest: Pinned TauCeti real algebraic dependency for entire boundary recovery. -/

/- Source: TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2,
TauCeti/Algebra/Polynomial/Rolle.lean.
Adaptation: ordinary D5 import routes; selected declarations retain their original proofs.
License: docs/reports/licenses/TauCeti-LICENSE.txt. Original copyright notices follow.
Retire each transplanted declaration when the actual pinned mathlib supplies an equivalent
statement, and replace its consumers by direct imports and applications of that pinned owner.
This adaptation contributes no independent mathematical novelty or escape credit. -/

/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.LinearCombination

/-! # Polynomial Rolle and mean value

`TauCeti.PolynomialRolle R` states that equal polynomial values at distinct endpoints give
an interior root of the formal derivative. From this explicit hypothesis,
`PolynomialRolle.exists_eval_sub_eq_derivative_eval_mul` derives polynomial mean value; over an
ordered field, `PolynomialRolle.monotoneOn`, `antitoneOn`, `strictMonoOn`, and `strictAntiOn`
derive the corresponding order properties from derivative signs.

`TauCeti.FieldTheory.RealClosure.AbstractRolle` supplies this hypothesis from `IsRealClosed`
and exports direct `Polynomial` versions of these results for real closed ordered fields.
The `IsRealClosed ℝ` instance specializes those statements to the real numbers.
-/

public section

open Polynomial Set

namespace TauCeti

/-- Polynomial Rolle: whenever a polynomial takes equal values at `a < b`, its formal
derivative has a root in `Ioo a b`. -/
@[expose]
def PolynomialRolle (R : Type*) [Field R] [LinearOrder R] : Prop :=
  ∀ (p : R[X]) (a b : R), a < b → p.eval a = p.eval b →
    ∃ c ∈ Ioo a b, p.derivative.eval c = 0

variable {R : Type*} [Field R] [LinearOrder R]

/-- Equal polynomial values at distinct endpoints give an interior derivative root. -/
theorem PolynomialRolle.exists_derivative_root (h : PolynomialRolle R) (p : R[X]) {a b : R}
    (hab : a < b) (heq : p.eval a = p.eval b) :
    ∃ c ∈ Ioo a b, p.derivative.eval c = 0 := h p a b hab heq

/-- Polynomial Rolle implies the mean value equality
`p.eval b - p.eval a = p.derivative.eval c * (b - a)` at some point `c ∈ Ioo a b`. -/
theorem PolynomialRolle.exists_eval_sub_eq_derivative_eval_mul
    (h : PolynomialRolle R) (p : R[X]) {a b : R} (hab : a < b) :
    ∃ c ∈ Ioo a b, p.eval b - p.eval a = p.derivative.eval c * (b - a) := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
  set m := (p.eval b - p.eval a) / (b - a)
  have hm : m * (b - a) = p.eval b - p.eval a := div_mul_cancel₀ _ hba
  obtain ⟨c, hc, hd⟩ := h.exists_derivative_root (p - C m * X) hab (by
    simp only [eval_sub, eval_mul, eval_C, eval_X]
    linear_combination hm)
  have hd' : p.derivative.eval c = m := by simpa [sub_eq_zero] using hd
  exact ⟨c, hc, by rw [hd', hm]⟩

/-- The mean value point for a subinterval lies in the surrounding open interval. -/
private theorem PolynomialRolle.exists_sub_eq (h : PolynomialRolle R) (p : R[X]) {a b u v : R}
    (hu : u ∈ Icc a b) (hv : v ∈ Icc a b) (huv : u < v) :
    ∃ c ∈ Ioo a b, p.eval v - p.eval u = p.derivative.eval c * (v - u) := by
  obtain ⟨c, hc, he⟩ := h.exists_eval_sub_eq_derivative_eval_mul p huv
  exact ⟨c, ⟨hu.1.trans_lt hc.1, hc.2.trans_le hv.2⟩, he⟩

variable [IsStrictOrderedRing R]

/-- Polynomial Rolle implies monotonicity where the derivative is nonnegative. -/
theorem PolynomialRolle.monotoneOn (h : PolynomialRolle R) (p : R[X]) {a b : R}
    (hd : ∀ x ∈ Ioo a b, 0 ≤ p.derivative.eval x) : MonotoneOn p.eval (Icc a b) := by
  intro u hu v hv huv
  rcases huv.eq_or_lt with rfl | huv
  · exact le_rfl
  obtain ⟨c, hc, he⟩ := h.exists_sub_eq p hu hv huv
  rw [← sub_nonneg, he]
  exact mul_nonneg (hd c hc) (sub_pos.mpr huv).le

/-- Polynomial Rolle implies antitonicity where the derivative is nonpositive. -/
theorem PolynomialRolle.antitoneOn (h : PolynomialRolle R) (p : R[X]) {a b : R}
    (hd : ∀ x ∈ Ioo a b, p.derivative.eval x ≤ 0) : AntitoneOn p.eval (Icc a b) := by
  intro u hu v hv huv
  rcases huv.eq_or_lt with rfl | huv
  · exact le_rfl
  obtain ⟨c, hc, he⟩ := h.exists_sub_eq p hu hv huv
  rw [← sub_nonpos, he]
  exact mul_nonpos_of_nonpos_of_nonneg (hd c hc) (sub_pos.mpr huv).le

/-- Strict positivity of the derivative gives strict monotonicity. -/
theorem PolynomialRolle.strictMonoOn (h : PolynomialRolle R) (p : R[X]) {a b : R}
    (hd : ∀ x ∈ Ioo a b, 0 < p.derivative.eval x) : StrictMonoOn p.eval (Icc a b) := by
  intro u hu v hv huv
  obtain ⟨c, hc, he⟩ := h.exists_sub_eq p hu hv huv
  rw [← sub_pos, he]
  exact mul_pos (hd c hc) (sub_pos.mpr huv)

/-- Strict negativity of the derivative gives strict antitonicity. -/
theorem PolynomialRolle.strictAntiOn (h : PolynomialRolle R) (p : R[X]) {a b : R}
    (hd : ∀ x ∈ Ioo a b, p.derivative.eval x < 0) : StrictAntiOn p.eval (Icc a b) := by
  intro u hu v hv huv
  obtain ⟨c, hc, he⟩ := h.exists_sub_eq p hu hv huv
  rw [← sub_neg, he]
  exact mul_neg_of_neg_of_pos (hd c hc) (sub_pos.mpr huv)

end TauCeti
