/- GID: D5/S3/Observer/GoldenCoding/GoldenRationalShellRigidity
   generality: I
   mirror-B: D5/B/S3/Observer/GoldenCoding/GoldenRationalShellRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Nonzero rational scales cannot collide under a positive golden shell translation. -/

import D5.S3.Observer.GoldenCoding.PrimeGoldenScaleCoordinate

/-!
This owner closes the algebraic core needed by a future quotient-circle
injectivity theorem.  A positive power of the orientation-preserving golden
unit `φ²` is irrational, so a nonzero rational scale cannot be translated by a
nontrivial natural shell depth and remain rational.

The theorem is exact.  It does not provide a quantitative lower bound for
near-collisions at finite precision, and it does not yet identify equality in
the additive-circle quotient with an integer shell displacement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.GoldenCoding.GoldenRationalShellRigidity

open scoped goldenRatio

/-- Every strictly positive natural power of the golden ratio is irrational. -/
theorem golden_ratio_positive_power_irrational (n : ℕ) :
    Irrational (Real.goldenRatio ^ (n + 1)) := by
  have hFibPos : 0 < Nat.fib (n + 1) :=
    Nat.fib_pos.mpr (Nat.succ_pos n)
  have hFibIrr :
      Irrational
        (Real.goldenRatio * (Nat.fib (n + 1) : ℝ) +
          (Nat.fib n : ℝ)) := by
    exact
      (Real.goldenRatio_irrational.mul_natCast (ne_of_gt hFibPos)).add_natCast
        (Nat.fib n)
  rw [Real.goldenRatio_mul_fib_succ_add_fib n] at hFibIrr
  exact hFibIrr

/-- Every positive natural power of the orientation-preserving golden unit is
irrational. -/
theorem golden_square_positive_power_irrational (n : ℕ) :
    Irrational ((Real.goldenRatio ^ 2) ^ (n + 1)) := by
  have hPower :
      (Real.goldenRatio ^ 2) ^ (n + 1) =
        Real.goldenRatio ^ ((2 * n + 1) + 1) := by
    calc
      (Real.goldenRatio ^ 2) ^ (n + 1) =
          Real.goldenRatio ^ (2 * (n + 1)) := (pow_mul _ _ _).symm
      _ = Real.goldenRatio ^ ((2 * n + 1) + 1) := by
        congr 1
        omega
  rw [hPower]
  exact golden_ratio_positive_power_irrational (2 * n + 1)

/-- If one nonzero rational scale is obtained from another by a natural golden
shell translation, then the shell depth is zero. -/
theorem rational_shell_collision_implies_zero
    {q₁ q₂ : ℚ} (hq₂ : q₂ ≠ 0) {n : ℕ}
    (hCollision :
      (q₁ : ℝ) = (Real.goldenRatio ^ 2) ^ n * (q₂ : ℝ)) :
    n = 0 := by
  by_contra hNonzero
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hNonzero
  have hq₂Real : (q₂ : ℝ) ≠ 0 := by
    exact_mod_cast hq₂
  have hPowerRat :
      (Real.goldenRatio ^ 2) ^ (m + 1) = ((q₁ / q₂ : ℚ) : ℝ) := by
    rw [Rat.cast_div]
    exact (eq_div_iff hq₂Real).2 hCollision.symm
  exact
    (golden_square_positive_power_irrational m).ne_rat (q₁ / q₂) hPowerRat

/-- The only natural-depth golden-shell collision between nonzero rationals is
the identity collision. -/
theorem rational_shell_collision_rigidity
    {q₁ q₂ : ℚ} (hq₂ : q₂ ≠ 0) {n : ℕ}
    (hCollision :
      (q₁ : ℝ) = (Real.goldenRatio ^ 2) ^ n * (q₂ : ℝ)) :
    n = 0 ∧ q₁ = q₂ := by
  have hDepth := rational_shell_collision_implies_zero hq₂ hCollision
  subst n
  simp only [pow_zero, one_mul] at hCollision
  refine ⟨rfl, ?_⟩
  exact_mod_cast hCollision

/-- The hypotheses are inhabited at zero shell depth. -/
example (q : ℚ) (hq : q ≠ 0) :
    (0 : ℕ) = 0 ∧ q = q :=
  rational_shell_collision_rigidity hq (by simp)

#print axioms golden_ratio_positive_power_irrational
#print axioms golden_square_positive_power_irrational
#print axioms rational_shell_collision_implies_zero
#print axioms rational_shell_collision_rigidity

end D5.S3.Observer.GoldenCoding.GoldenRationalShellRigidity
