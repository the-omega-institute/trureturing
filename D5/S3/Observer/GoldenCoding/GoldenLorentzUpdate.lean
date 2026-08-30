/- GID: D5/S3/Observer/GoldenCoding/GoldenLorentzUpdate
   generality: I
   mirror-B: D5/B/S3/Observer/GoldenCoding/GoldenLorentzUpdate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Fibonacci updates negate the golden Lorentz form once and preserve it twice. -/

import D5.S1.Scale.FibonacciEigen
import Mathlib.Tactic

/- Library-search audit trail (2026-08-30):
   * Current-tree name and body-shape searches for Fibonacci anti-isometries,
     golden Lorentz forms, `(x + y, x)`, and `x^2 - x*y - y^2` found no exact
     frozen theorem or existing definition of the source quadratic form.
   * `D5.S1.Scale.fibonacciSubstitution` is the canonical real Fibonacci matrix
     and is imported rather than redeclared.
   * Pinned Mathlib supplies generic quadratic-form isometry APIs and matrix
     multiplication lemmas, but no exact result for this matrix and form. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Matrix

namespace D5.S3.Observer.GoldenCoding.GoldenLorentzUpdate

open D5.S1.Scale

/-- For the source quadratic form `Q(x,y) = x^2 - xy - y^2`, one Fibonacci
update negates `Q`, two updates preserve it, and the positive and negative
Lorentz sectors are exchanged by one update. -/
theorem golden_lorentz_update :
    let Q := fun v : Fin 2 -> ℝ =>
      v 0 ^ 2 - v 0 * v 1 - v 1 ^ 2
    (forall v, Q (fibonacciSubstitution *ᵥ v) = -Q v) /\
      (forall v, Q ((fibonacciSubstitution ^ 2) *ᵥ v) = Q v) /\
      (forall v, 0 < Q v -> Q (fibonacciSubstitution *ᵥ v) < 0) /\
      (forall v, Q v < 0 -> 0 < Q (fibonacciSubstitution *ᵥ v)) := by
  dsimp only
  have hAnti : forall v : Fin 2 -> ℝ,
      (fibonacciSubstitution *ᵥ v) 0 ^ 2 -
          (fibonacciSubstitution *ᵥ v) 0 * (fibonacciSubstitution *ᵥ v) 1 -
          (fibonacciSubstitution *ᵥ v) 1 ^ 2 =
        -(v 0 ^ 2 - v 0 * v 1 - v 1 ^ 2) := by
    intro v
    simp [fibonacciSubstitution, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  have hDouble : forall v : Fin 2 -> ℝ,
      ((fibonacciSubstitution ^ 2) *ᵥ v) 0 ^ 2 -
          ((fibonacciSubstitution ^ 2) *ᵥ v) 0 *
            ((fibonacciSubstitution ^ 2) *ᵥ v) 1 -
          ((fibonacciSubstitution ^ 2) *ᵥ v) 1 ^ 2 =
        v 0 ^ 2 - v 0 * v 1 - v 1 ^ 2 := by
    intro v
    rw [show fibonacciSubstitution ^ 2 =
      fibonacciSubstitution * fibonacciSubstitution by rw [pow_two]]
    rw [<- Matrix.mulVec_mulVec, hAnti, hAnti, neg_neg]
  refine ⟨hAnti, hDouble, ?_, ?_⟩
  · intro v hPositive
    rw [hAnti]
    exact neg_neg_of_pos hPositive
  · intro v hNegative
    rw [hAnti]
    exact neg_pos.mpr hNegative

#print axioms golden_lorentz_update

end D5.S3.Observer.GoldenCoding.GoldenLorentzUpdate
