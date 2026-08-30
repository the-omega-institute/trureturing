/- GID: D5/S3/Observer/GoldenCoding/GoldenRationalShellRigidity
   generality: I
   mirror-B: D5/B/S3/Observer/GoldenCoding/GoldenRationalShellRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Positive golden-shell powers cannot carry one nonzero rational scale
     to another unless the shell depth is zero. -/

import D5.S3.Observer.GoldenCoding.PrimeGoldenScaleCoordinate

/-!
The golden scale circle identifies logarithmic coordinates modulo the period
`2 * log phi`. Before introducing the quotient, this module proves its key
arithmetic rigidity statement on the universal cover: a nontrivial positive
power of `phi^2` is irrational, so it cannot carry one nonzero rational scale
to another rational scale.

This is an exact algebraic statement. It does not claim a quantitative lower
bound for near-collisions of phases at finite precision.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.GoldenCoding.GoldenRationalShellRigidity

open scoped goldenRatio
open D5.S3.CompletionDynamics.GoldenMobius.GoldenScaleHelix
open D5.S3.Observer.GoldenCoding.PrimeGoldenScaleCoordinate

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
      (Real.goldenRatio_irrational.mul_natCast
          (ne_of_gt hFibPos)).add_natCast
        (Nat.fib n)
  rw [Real.goldenRatio_mul_fib_succ_add_fib n] at hFibIrr
  exact hFibIrr

/-- Every positive power of the orientation-preserving golden unit `phi^2` is
irrational. -/
theorem golden_square_positive_power_irrational (n : ℕ) :
    Irrational ((Real.goldenRatio ^ 2) ^ (n + 1)) := by
  have hPower :
      (Real.goldenRatio ^ 2) ^ (n + 1) =
        Real.goldenRatio ^ ((2 * n + 1) + 1) := by
    calc
      (Real.goldenRatio ^ 2) ^ (n + 1) =
          Real.goldenRatio ^ (2 * (n + 1)) :=
        (pow_mul _ _ _).symm
      _ = Real.goldenRatio ^ ((2 * n + 1) + 1) := by
        congr 1
  rw [hPower]
  exact golden_ratio_positive_power_irrational (2 * n + 1)

/-- A rational scale cannot be translated by a nontrivial positive golden
shell and remain rational. -/
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
      (Real.goldenRatio ^ 2) ^ (m + 1) =
        ((q₁ / q₂ : ℚ) : ℝ) := by
    rw [Rat.cast_div]
    exact (eq_div_iff hq₂Real).2 hCollision.symm
  exact
    (golden_square_positive_power_irrational m).ne_rat
      (q₁ / q₂) hPowerRat

/-- The only positive golden-shell collision between nonzero rationals is the
zero-depth identity collision. -/
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

/-- Equality of positive rational golden coordinates up to a natural shell
translation is possible only at zero depth. -/
theorem rational_coordinate_shell_rigidity
    {q₁ q₂ : ℚ} (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) {n : ℕ}
    (hCoordinate :
      goldenScaleCoordinate (q₁ : ℝ) =
        goldenScaleCoordinate (q₂ : ℝ) + n) :
    n = 0 ∧ q₁ = q₂ := by
  have hPeriodNe : goldenScalePeriod ≠ 0 :=
    ne_of_gt golden_scale_period_pos
  have hLogEq :
      Real.log (q₁ : ℝ) =
        Real.log (q₂ : ℝ) + (n : ℝ) * goldenScalePeriod := by
    calc
      Real.log (q₁ : ℝ) =
          goldenScaleCoordinate (q₁ : ℝ) * goldenScalePeriod := by
        unfold goldenScaleCoordinate
        field_simp [hPeriodNe]
      _ =
          (goldenScaleCoordinate (q₂ : ℝ) + n) *
            goldenScalePeriod := by
        rw [hCoordinate]
      _ =
          Real.log (q₂ : ℝ) + (n : ℝ) * goldenScalePeriod := by
        unfold goldenScaleCoordinate
        field_simp [hPeriodNe]
  have hLogUnit :
      Real.log ((Real.goldenRatio ^ 2) ^ n) =
        (n : ℝ) * goldenScalePeriod := by
    rw [Real.log_pow, Real.log_pow]
    unfold goldenScalePeriod
    ring
  have hq₁Real : 0 < (q₁ : ℝ) := by exact_mod_cast hq₁
  have hq₂Real : 0 < (q₂ : ℝ) := by exact_mod_cast hq₂
  have hUnitPos : 0 < (Real.goldenRatio ^ 2) ^ n := by
    positivity
  have hLogs :
      Real.log (q₁ : ℝ) =
        Real.log ((Real.goldenRatio ^ 2) ^ n * (q₂ : ℝ)) := by
    calc
      Real.log (q₁ : ℝ) =
          Real.log (q₂ : ℝ) + (n : ℝ) * goldenScalePeriod :=
        hLogEq
      _ =
          Real.log ((Real.goldenRatio ^ 2) ^ n) +
            Real.log (q₂ : ℝ) := by
        rw [hLogUnit]
        ring
      _ =
          Real.log ((Real.goldenRatio ^ 2) ^ n * (q₂ : ℝ)) := by
        rw [Real.log_mul hUnitPos.ne' hq₂Real.ne']
  have hCollision :
      (q₁ : ℝ) = (Real.goldenRatio ^ 2) ^ n * (q₂ : ℝ) := by
    exact Real.strictMonoOn_log.injOn
      hq₁Real (mul_pos hUnitPos hq₂Real) hLogs
  exact rational_shell_collision_rigidity hq₂.ne' hCollision

/-- The hypotheses are inhabited by every positive rational at zero depth. -/
example (q : ℚ) (hq : 0 < q) :
    (0 : ℕ) = 0 ∧ q = q :=
  rational_coordinate_shell_rigidity hq hq (by norm_num)

#print axioms golden_ratio_positive_power_irrational
#print axioms golden_square_positive_power_irrational
#print axioms rational_shell_collision_implies_zero
#print axioms rational_shell_collision_rigidity
#print axioms rational_coordinate_shell_rigidity

end D5.S3.Observer.GoldenCoding.GoldenRationalShellRigidity
