/- GID: D5/S1/Recurrence/PrimeSquareDoubleRootObstruction
   generality: G
   mirror-B: none(waiver:new-source-refutation)
   mirror-E: none(waiver:universal-polynomial-obstruction)
   anchors: []
   digest: The unchanged double-root factor cannot divide X^n-1 over ZMod(n^2) for any n>1, refuting the literal coefficient conjecture in arXiv:2603.25343v1 section 4.3. -/

import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S1.Recurrence.PrimeSquareDoubleRootObstruction

open Polynomial

/-- A repeated linear factor forces the derivative to vanish at its root over any commutative ring. -/
private lemma derivative_at_double_root {R : Type*} [CommRing R] (a : R) (f : R[X])
    (h : (X - C a) ^ 2 ∣ f) : eval a (derivative f) = 0 := by
  obtain ⟨g, rfl⟩ := h
  simp [pow_two, derivative_mul, derivative_sub]

/-- The literal unchanged-factor conjecture fails uniformly; primality is not required. -/
theorem unchanged_double_root_not_dvd (n : ℕ) (hn : 1 < n) :
    ¬ ((X - 1 : (ZMod (n ^ 2))[X]) ^ 2 ∣ X ^ n - 1) := by
  intro h
  have hz := derivative_at_double_root (1 : ZMod (n ^ 2)) (X ^ n - 1)
    (by simpa using h)
  have hnzero : (n : ZMod (n ^ 2)) = 0 := by
    simpa [derivative_sub, derivative_X_pow] using hz
  have hdiv : n ^ 2 ∣ n := (ZMod.natCast_eq_zero_iff n (n ^ 2)).mp hnzero
  have hle : n ^ 2 ≤ n := Nat.le_of_dvd (by omega) hdiv
  nlinarith

/-- The coefficients a=-2,b=1 named in the paper are exactly the excluded factor. -/
theorem conjectured_quadratic_not_dvd (n : ℕ) (hn : 1 < n) :
    ¬ ((X ^ 2 - C (2 : ZMod (n ^ 2)) * X + 1 : (ZMod (n ^ 2))[X]) ∣
      X ^ n - 1) := by
  have he : (X ^ 2 - C (2 : ZMod (n ^ 2)) * X + 1 : (ZMod (n ^ 2))[X]) =
      (X - 1) ^ 2 := by
    norm_num <;> ring
  rw [he]
  exact unchanged_double_root_not_dvd n hn

end D5.S1.Recurrence.PrimeSquareDoubleRootObstruction
