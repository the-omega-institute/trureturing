/- GID: D5/S3/Quantum/Matrix/PauliFunding/PureYAxisResolvent
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/PauliFunding/PureYAxisResolvent
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Exact parity resolvents and all-order moments of real two-dimensional control blocks. -/

import D5.S3.Quantum.Matrix.PauliFunding.ParityTraceComparison
import D5.S3.Quantum.Measurement.FreeSpectrahedronFeasibilityWitness
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Matrix.PauliFunding

open Matrix
open scoped MatrixOrder ComplexOrder

/-- The actual real control block, with transverse Bloch coordinate `t`. -/
def controlBlock (a t : ℝ) : Mat := !![(1 + a) / 4, t / 4; t / 4, (1 - a) / 4]

/-- The shifted filter of the actual control block. -/
def controlFilter (a t s : ℝ) : Mat :=
  controlBlock a t * (controlBlock a t + s • 1)⁻¹

/-- Four times four times the determinant of the control block. -/
def h (a t : ℝ) : ℝ := 1 - a ^ 2 - t ^ 2

/-- The determinant numerator of the shifted control block. -/
def denom (a t s : ℝ) : ℝ := 8 * s * (1 + 2 * s) + h a t

/-- Half the trace of the parity times the positive filter. -/
def alpha (a t s : ℝ) : ℝ := 4 * s * a / denom a t s

/-- The negative determinant of the parity times the positive filter. -/
def beta (a t s : ℝ) : ℝ := h a t / denom a t s

/-- The cyclic real product moment of the two actual shifted filters. -/
def moment (a t : ℝ) (j : ℕ) (s : ℝ) : ℝ :=
  trace ((controlFilter a (-t) s * controlFilter a t s) ^ j)

private theorem denom_pos {a t s : ℝ} (ht : t ^ 2 ≤ 1 - a ^ 2) (hs : 0 < s) :
    0 < denom a t s := by
  unfold denom h
  have : 0 < 8 * s * (1 + 2 * s) := by positivity
  linarith

private theorem shifted_inverse {a t s : ℝ} (ht : t ^ 2 ≤ 1 - a ^ 2) (hs : 0 < s) :
    (controlBlock a t + s • 1)⁻¹ =
      (4 / denom a t s) • !![1 - a + 4 * s, -t; -t, 1 + a + 4 * s] := by
  have hd : denom a t s ≠ 0 := ne_of_gt (denom_pos ht hs)
  apply Matrix.inv_eq_right_inv
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [controlBlock, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply,
      Matrix.smul_apply, smul_eq_mul] <;>
    field_simp [hd] <;> dsimp [denom, h] <;> ring

private theorem filter_formula {a t s : ℝ} (ht : t ^ 2 ≤ 1 - a ^ 2) (hs : 0 < s) :
    controlFilter a t s =
      !![(4 * s + h a t + 4 * s * a) / denom a t s, 4 * s * t / denom a t s;
         4 * s * t / denom a t s, (4 * s + h a t - 4 * s * a) / denom a t s] := by
  have hd : denom a t s ≠ 0 := ne_of_gt (denom_pos ht hs)
  unfold controlFilter
  rw [shifted_inverse ht hs]
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [controlBlock, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply,
      smul_eq_mul] <;> field_simp [hd] <;> dsimp [h] <;> ring

private theorem filter_parity {a t s : ℝ} (ht : t ^ 2 ≤ 1 - a ^ 2) (hs : 0 < s) :
    controlFilter a (-t) s = parity * controlFilter a t s * parity := by
  rw [filter_formula ht hs, filter_formula (by simpa using ht) hs]
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [parity, denom, h, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem product_eq_square {a t s : ℝ}
    (ht : t ^ 2 ≤ 1 - a ^ 2) (hs : 0 < s) :
    controlFilter a (-t) s * controlFilter a t s = (parity * controlFilter a t s) ^ 2 := by
  rw [filter_parity ht hs, pow_two]
  simp only [Matrix.mul_assoc]

/-- Exact resolvent data, including the singular unshifted boundary. Every inverse is
shifted by a strictly positive scalar; positivity of the determinant is derived. -/
theorem resolvent_spectral_data {a t s : ℝ} (ha0 : 0 ≤ a) (_ha1 : a ≤ 1)
    (ht : t ^ 2 ≤ 1 - a ^ 2) (hs : 0 < s) :
    0 < denom a t s ∧ 0 ≤ alpha a t s ∧ 0 ≤ beta a t s ∧
      controlFilter a t s =
        !![(4 * s + h a t + 4 * s * a) / denom a t s, 4 * s * t / denom a t s;
           4 * s * t / denom a t s, (4 * s + h a t - 4 * s * a) / denom a t s] ∧
      controlFilter a (-t) s = parity * controlFilter a t s * parity ∧
      trace (parity * controlFilter a t s) = 2 * alpha a t s ∧
      det (parity * controlFilter a t s) = -beta a t s := by
  have hd := denom_pos ht hs
  have hd0 := ne_of_gt hd
  refine ⟨hd, div_nonneg (by positivity) hd.le,
    div_nonneg (by dsimp [h]; linarith) hd.le,
    filter_formula ht hs, filter_parity ht hs, ?_, ?_⟩
  · rw [filter_formula ht hs]
    simp [parity, alpha, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · rw [filter_formula ht hs]
    simp [parity, beta, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    field_simp [hd0]
    dsimp [denom, h]
    ring

/-- The full matrix product moment is the exact even power sum at every order. -/
theorem moment_eq_evenMoment {a t s : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (ht : t ^ 2 ≤ 1 - a ^ 2) (hs : 0 < s) (j : ℕ) :
    moment a t j s = evenMoment (alpha a t s) (beta a t s) j := by
  obtain ⟨_, _, hb, _, _, htr, hdet⟩ := resolvent_spectral_data ha0 ha1 ht hs
  unfold moment
  rw [product_eq_square ht hs, ← pow_mul]
  exact even_trace_formula _ _ _ hb htr hdet j

private theorem comparison_polynomial {a t s : ℝ}
    (ht : t ^ 2 ≤ 1 - a ^ 2) (hs : 0 < s) :
    (a / (1 + 2 * s)) ^ 2 - 2 * alpha a t s * (a / (1 + 2 * s)) - beta a t s =
      beta a t s * ((a / (1 + 2 * s)) ^ 2 - 1) := by
  have hd0 := ne_of_gt (denom_pos ht hs)
  have hq0 : 1 + 2 * s ≠ 0 := by positivity
  unfold alpha beta
  field_simp [hd0, hq0]
  dsimp [denom]
  ring

/-- Pointwise comparison for every actual matrix moment. -/
theorem moment_comparison {a t s : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (ht : t ^ 2 ≤ 1 - a ^ 2) (hs : 0 < s) (j : ℕ) :
    a ^ (2 * j) / (1 + 2 * s) ^ (2 * j) ≤ moment a t j s := by
  obtain ⟨_, ha, hb, _, _, htr, hdet⟩ := resolvent_spectral_data ha0 ha1 ht hs
  have hq : 0 < 1 + 2 * s := by positivity
  have hc : 0 ≤ a / (1 + 2 * s) := div_nonneg ha0 hq.le
  have hc1 : a / (1 + 2 * s) ≤ 1 := (div_le_one hq).mpr (by linarith)
  have hp : (a / (1 + 2 * s)) ^ 2 - 2 * alpha a t s * (a / (1 + 2 * s)) -
      beta a t s ≤ 0 := by
    rw [comparison_polynomial ht hs]
    exact mul_nonpos_of_nonneg_of_nonpos hb (by nlinarith)
  unfold moment
  rw [product_eq_square ht hs, ← pow_mul, ← div_pow]
  exact even_trace_comparison _ _ _ _ ha hb hc htr hdet hp j

/-- Strict comparison at all positive orders whenever the actual block determinant is positive. -/
theorem moment_strict {a t s : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (ht : t ^ 2 ≤ 1 - a ^ 2) (hh : 0 < h a t) (hs : 0 < s) (j : ℕ) (hj : 1 ≤ j) :
    a ^ (2 * j) / (1 + 2 * s) ^ (2 * j) < moment a t j s := by
  obtain ⟨hd, ha, hb, _, _, htr, hdet⟩ := resolvent_spectral_data ha0 ha1 ht hs
  have hq : 0 < 1 + 2 * s := by positivity
  have hc : 0 ≤ a / (1 + 2 * s) := div_nonneg ha0 hq.le
  have hc1 : a / (1 + 2 * s) < 1 := (div_lt_one hq).mpr (by linarith)
  have hbp : 0 < beta a t s := div_pos hh hd
  have hp : (a / (1 + 2 * s)) ^ 2 - 2 * alpha a t s * (a / (1 + 2 * s)) -
      beta a t s < 0 := by
    rw [comparison_polynomial ht hs]
    exact mul_neg_of_pos_of_neg hbp (by nlinarith)
  unfold moment
  rw [product_eq_square ht hs, ← pow_mul, ← div_pow]
  exact even_trace_strict _ _ _ _ ha hb hc htr hdet hp j hj

/-- On the rank-one boundary the all-order matrix moment equals the reference moment. -/
theorem moment_boundary {a t s : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (ht : t ^ 2 ≤ 1 - a ^ 2) (hh : h a t = 0) (hs : 0 < s) (j : ℕ) (hj : 1 ≤ j) :
    moment a t j s = a ^ (2 * j) / (1 + 2 * s) ^ (2 * j) := by
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hq0 : 1 + 2 * s ≠ 0 := by positivity
  have hb : beta a t s = 0 := by simp [beta, hh]
  have ha : 0 ≤ alpha a t s := (resolvent_spectral_data ha0 ha1 ht hs).2.1
  have hα : 2 * alpha a t s = a / (1 + 2 * s) := by
    unfold alpha denom
    rw [hh]
    field_simp [hs0, hq0]
    <;> ring
  rw [moment_eq_evenMoment ha0 ha1 ht hs, evenMoment, hb, add_zero,
    Real.sqrt_sq ha, sub_self, zero_pow (by omega), add_zero]
  rw [← div_pow, ← hα]
  congr 1
  ring

#print axioms resolvent_spectral_data
#print axioms moment_eq_evenMoment
#print axioms moment_comparison
#print axioms moment_strict
#print axioms moment_boundary

end D5.S3.Quantum.Matrix.PauliFunding
