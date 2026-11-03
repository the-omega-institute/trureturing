/- GID: D5/S3/Zeros/Resolvent/ActualXiTaylorBounds
   generality: I
   mirror-B: D5/B/S3/Zeros/Resolvent/ActualXiTaylorBounds
   mirror-E: none(waiver:actual-analytic-zero-source)
   anchors: []
   utility: none
   digest: Normal convergence and geometric Taylor remainders for the original actual xi expression. -/

import D5.S3.Zeros.Resolvent.ActualXiTaylorDictionary
import Mathlib.Tactic

/-! Uniform absolute majorants and geometric remainders for the actual xi dictionary. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Zeros.Resolvent.ActualXiTaylorBounds
open Complex Filter Finset
open D5.S3.Zeros.Resolvent.ActualXiFoldedSpectrum
open D5.S3.Zeros.Resolvent.ActualXiFoldedResolvent
open D5.S3.Zeros.Resolvent.ActualXiTaylorDictionary
open scoped Topology

private theorem ratio_bounds (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1 / 4) :
    0 ≤ radius * r ^ 2 ∧ radius * r ^ 2 < 1 := by
  have hΛ := radius_bounds.1
  have h := mul_le_mul_of_nonneg_right radius_bounds.2 (sq_nonneg r)
  constructor
  · positivity
  · nlinarith

private theorem power_term_bound (r : ℝ) (hr : 0 ≤ r) (w : ℂ) (hw : ‖w‖ ≤ r) (j : ℕ) :
    ‖moment j * w ^ (2 * j + 1)‖ ≤ totalWeight * r * (radius * r ^ 2) ^ j := by
  have hW : 0 ≤ totalWeight := tsum_nonneg (fun _ => norm_nonneg _)
  have hΛ := radius_bounds.1
  rw [norm_mul, norm_pow]
  calc
    ‖moment j‖ * ‖w‖ ^ (2 * j + 1) ≤
        (totalWeight * radius ^ j) * r ^ (2 * j + 1) := by
      gcongr
      exact moment_bound j
    _ = totalWeight * r * (radius * r ^ 2) ^ j := by rw [mul_pow, pow_add, pow_mul]; ring

private theorem folded_term_bound (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1 / 4)
    (w : ℂ) (hw : ‖w‖ ≤ r) (n : PositiveZero) :
    ‖w * weight n / (1 - node n * w ^ 2)‖ ≤
      ‖weight n‖ * r / (1 - radius * r ^ 2) := by
  have hΛ := radius_bounds.1
  have hq := ratio_bounds r hr hr1
  have hd : 1 - radius * r ^ 2 ≤ ‖1 - node n * w ^ 2‖ := by
    have ht := norm_sub_norm_le (1 : ℂ) (node n * w ^ 2)
    rw [norm_one, norm_mul, norm_pow] at ht
    have hm : ‖node n‖ * ‖w‖ ^ 2 ≤ radius * r ^ 2 := by
      gcongr
      exact node_norm_le_radius n
    linarith
  rw [norm_div, norm_mul]
  calc
    ‖w‖ * ‖weight n‖ / ‖1 - node n * w ^ 2‖ ≤
        r * ‖weight n‖ / (1 - radius * r ^ 2) := by
      apply div_le_div₀ (by positivity) (by gcongr) (by linarith) hd
    _ = ‖weight n‖ * r / (1 - radius * r ^ 2) := by ring

/-- A summable majorant on every closed subdisk proves normal folded convergence. -/
theorem actual_xi_folded_normal (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1 / 4) :
    Summable (fun n : PositiveZero => ‖weight n‖ * r / (1 - radius * r ^ 2)) ∧
    HasSumUniformlyOn (fun n : PositiveZero => fun w : ℂ =>
      w * weight n / (1 - node n * w ^ 2)) xiOdd (Metric.closedBall 0 r) := by
  have hs := (weight_norm_summable.mul_right r).div_const (1 - radius * r ^ 2)
  refine ⟨hs, ?_⟩
  have hu := HasSumUniformlyOn.of_norm_le_summable (s := Metric.closedBall (0 : ℂ) r)
    hs (fun n w hw =>
    folded_term_bound r hr hr1 w (by simpa using hw) n)
  apply hu.congr_right (fun w hw => ?_)
  exact (actual_xi_folded_hasSum w ((show ‖w‖ ≤ r by simpa using hw).trans_lt hr1)).tsum_eq

/-- Compact-disk bound using the actual supremum of the folded node norms. -/
theorem actual_xi_disk_bound (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1 / 4)
    (w : ℂ) (hw : ‖w‖ ≤ r) :
    ‖xiOdd w‖ ≤ totalWeight * r / (1 - radius * r ^ 2) := by
  have hs := (weight_norm_summable.hasSum.mul_right r).div_const (1 - radius * r ^ 2)
  exact (actual_xi_folded_hasSum w (hw.trans_lt hr1)).norm_le_of_bounded hs
    (fun n => folded_term_bound r hr hr1 w hw n)

/-- The actual moment series also converges normally on each closed subdisk. -/
theorem actual_xi_taylor_normal (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1 / 4) :
    Summable (fun j : ℕ => totalWeight * r * (radius * r ^ 2) ^ j) ∧
    HasSumUniformlyOn (fun j : ℕ => fun w : ℂ => moment j * w ^ (2 * j + 1))
      xiOdd (Metric.closedBall 0 r) := by
  have hq := ratio_bounds r hr hr1
  have hs := (hasSum_geometric_of_lt_one hq.1 hq.2).summable.mul_left (totalWeight * r)
  refine ⟨hs, ?_⟩
  have hu := HasSumUniformlyOn.of_norm_le_summable (s := Metric.closedBall (0 : ℂ) r) hs
    (fun j w hw => power_term_bound r hr w (by simpa using hw) j)
  apply hu.congr_right (fun w hw => ?_)
  exact (actual_xi_moment_hasSum w ((show ‖w‖ ≤ r by simpa using hw).trans_lt hr1)).tsum_eq

/-- Uniform geometric remainder after the odd terms through index J. -/
theorem actual_xi_taylor_remainder (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1 / 4)
    (w : ℂ) (hw : ‖w‖ ≤ r) (J : ℕ) :
    ‖xiOdd w - ∑ j ∈ range (J + 1), moment j * w ^ (2 * j + 1)‖ ≤
      totalWeight * r * (radius * r ^ 2) ^ (J + 1) / (1 - radius * r ^ 2) := by
  have hq := ratio_bounds r hr hr1
  have hs := (actual_xi_moment_hasSum w (hw.trans_lt hr1)).summable
  have he := hs.sum_add_tsum_nat_add (J + 1)
  rw [(actual_xi_moment_hasSum w (hw.trans_lt hr1)).tsum_eq] at he
  have he' : xiOdd w - ∑ j ∈ range (J + 1), moment j * w ^ (2 * j + 1) =
      ∑' j : ℕ, moment (j + (J + 1)) * w ^ (2 * (j + (J + 1)) + 1) := by
    linear_combination -he
  rw [he']
  have hgeom := (hasSum_geometric_of_lt_one hq.1 hq.2).mul_left
    (totalWeight * r * (radius * r ^ 2) ^ (J + 1))
  have hval : totalWeight * r * (radius * r ^ 2) ^ (J + 1) * (1 - radius * r ^ 2)⁻¹ =
      totalWeight * r * (radius * r ^ 2) ^ (J + 1) / (1 - radius * r ^ 2) := by rfl
  rw [hval] at hgeom
  apply tsum_of_norm_bounded hgeom
  intro j
  calc
    ‖moment (j + (J + 1)) * w ^ (2 * (j + (J + 1)) + 1)‖ ≤
        totalWeight * r * (radius * r ^ 2) ^ (j + (J + 1)) := power_term_bound r hr w hw _
    _ = totalWeight * r * (radius * r ^ 2) ^ (J + 1) * (radius * r ^ 2) ^ j := by
      rw [pow_add]; ring

end D5.S3.Zeros.Resolvent.ActualXiTaylorBounds
