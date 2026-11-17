/- GID: D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticIntegral
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/MaximalHockeyStickQuadraticIntegral
   mirror-E: none(waiver:finite-matrix-proof)
   anchors: []
   utility: none
   digest: The actual quadratic perspective equals a compact hockey integral. -/

import D5.S3.Quantum.Divergence.MaximalHockeyStickQuadraticCanonical
import D5.S3.Quantum.Divergence.MaximalHockeyStickApproximate
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! An exact triangle integral represents the standard quadratic cost of each actual test. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Filter Matrix MeasureTheory Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology
open D5.S3.Quantum.Divergence.MaximalHockeyStickQuadratic
open D5.S3.Quantum.Divergence.MaximalHockeyStickApproximate
open D5.S3.Quantum.Divergence.MaximalHockeyStickReverseTest

namespace D5.S3.Quantum.Divergence.MaximalHockeyStickQuadraticIntegral

private theorem triangle_integral (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    (∫ u in (0 : ℝ)..1, max (p - u * (p + q)) 0) = p ^ 2 / (2 * (p + q)) := by
  by_cases hzero : p + q = 0
  · have hp0 : p = 0 := by linarith
    have hq0 : q = 0 := by linarith
    simp [hp0, hq0]
  have hs : 0 < p + q := lt_of_le_of_ne (add_nonneg hp hq) (Ne.symm hzero)
  let x := p / (p + q)
  have hx0 : 0 ≤ x := div_nonneg hp hs.le
  have hx1 : x ≤ 1 := (div_le_one hs).2 (by linarith)
  have hf : Continuous (fun u : ℝ => max (p - u * (p + q)) 0) := by fun_prop
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (μ := volume) (a := 0) (b := x))
    (hf.intervalIntegrable (μ := volume) (a := x) (b := 1))
  have hleft : (∫ u in (0 : ℝ)..x, max (p - u * (p + q)) 0) =
      p * x - (p + q) * x ^ 2 / 2 := by
    have hpint : IntervalIntegrable (fun _ : ℝ => p) volume 0 x :=
      continuous_const.intervalIntegrable 0 x
    have huint : IntervalIntegrable (fun u : ℝ => u * (p + q)) volume 0 x :=
      (continuous_id.mul continuous_const).intervalIntegrable 0 x
    calc
      _ = ∫ u in (0 : ℝ)..x, p - u * (p + q) := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [uIcc_of_le hx0] at hu
        apply max_eq_left
        have hux : u * (p + q) ≤ x * (p + q) := mul_le_mul_of_nonneg_right hu.2 hs.le
        have hxe : x * (p + q) = p := div_mul_cancel₀ p hzero
        linarith
      _ = _ := by
        rw [intervalIntegral.integral_sub hpint huint,
          intervalIntegral.integral_const, intervalIntegral.integral_mul_const,
          integral_id]
        simp only [sub_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          zero_div, smul_eq_mul]
        ring
  have hright : (∫ u in x..(1 : ℝ), max (p - u * (p + q)) 0) = 0 := by
    calc
      _ = ∫ _ in x..(1 : ℝ), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [uIcc_of_le hx1] at hu
        apply max_eq_right
        have hux : x * (p + q) ≤ u * (p + q) := mul_le_mul_of_nonneg_right hu.1 hs.le
        have hxe : x * (p + q) = p := div_mul_cancel₀ p hzero
        linarith
      _ = 0 := by simp
  rw [← hsplit, hleft, hright, add_zero]
  dsimp [x]
  field_simp [hzero]
  ring

/-- An exact finite-interval hockey representation of the standard closed
perspective `(p-q)^2/(p+q)`, including both axes and the origin. -/
theorem star_perspective_hockey_integral (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    starPerspective p q = q - 3 * p +
      8 * ∫ u in (0 : ℝ)..1, max (p - u * (p + q)) 0 := by
  rw [triangle_integral p q hp hq]
  unfold starPerspective
  by_cases hs : p + q = 0
  · have hp0 : p = 0 := by linarith
    have hq0 : q = 0 := by linarith
    simp [hp0, hq0]
  · field_simp [hs]
    ring

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The compact classical hockey profile of the actual test; it is defined
at both interval endpoints without a division. -/
def compactHockey {A B : Matrix n n ℂ} {k : ℕ} (R : ReverseTest A B k) (u : ℝ) : ℝ :=
  ∑ i, max (R.p i - u * (R.p i + R.q i)) 0

theorem compact_hockey_continuous {A B : Matrix n n ℂ} {k : ℕ}
    (R : ReverseTest A B k) : Continuous (compactHockey R) := by
  unfold compactHockey
  fun_prop

/-- On the open unit interval this is exactly the rescaled original hockey
profile, at the positive threshold `u/(1-u)`. -/
theorem compact_hockey_eq_scaled {A B : Matrix n n ℂ} {k : ℕ}
    (R : ReverseTest A B k) (u : ℝ) (hu : u < 1) :
    compactHockey R u = (1 - u) * R.hockey (u / (1 - u)) := by
  unfold compactHockey ReverseTest.hockey
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_max_of_nonneg _ _ (sub_nonneg.mpr hu.le), mul_zero]
  congr 1
  field_simp [ne_of_gt (sub_pos.mpr hu)]
  ring

/-- The exact reference identity uses the actual classical perspective cost
and the actual masses prepared by the test. -/
theorem star_cost_hockey_integral {A B : Matrix n n ℂ} {k : ℕ}
    (R : ReverseTest A B k) :
    R.starCost = B.trace.re - 3 * A.trace.re +
      8 * ∫ u in (0 : ℝ)..1, compactHockey R u := by
  unfold ReverseTest.starCost compactHockey
  simp_rw [star_perspective_hockey_integral _ _ (R.p_nonneg _) (R.q_nonneg _)]
  rw [intervalIntegral.integral_finsetSum (fun i _ => (by
    apply Continuous.intervalIntegrable
    fun_prop)), left_mass R, right_mass R]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]

end D5.S3.Quantum.Divergence.MaximalHockeyStickQuadraticIntegral
