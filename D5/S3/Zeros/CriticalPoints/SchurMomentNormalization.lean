/- GID: D5/S3/Zeros/CriticalPoints/SchurMomentNormalization
   generality: G
   mirror-B: D5/B/S3/Zeros/CriticalPoints/SchurMomentNormalization
   mirror-E: none(waiver:open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Pow.Real]
   utility: none
   digest: Normalized Schur diagonals and reciprocal critical-point moments. -/

import D5.S3.Zeros.CriticalPoints.RankOneComplexPowers
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Positive normalized weights for the scalar interpolation argument. -/

set_option autoImplicit false
noncomputable section

namespace D5.S3.Zeros.CriticalPoints.SchurMomentNormalization

open Matrix Complex
open scoped ComplexConjugate
open RankOneComplexPowers

theorem normalized_weights {n : ℕ} (hn : 0 < n) (μ : Fin n → ℂ)
    (hμ : ∀ k, μ k ≠ 0) (p : ℝ) (hp : 0 < p) :
    ∃ (N : ℝ) (ρ : Fin n → ℝ) (v : Fin n → ℂ),
      0 < N ∧ (∀ k, 0 < ρ k) ∧ (∀ k, ‖v k‖ = 1) ∧
      (∀ k, μ k = v k * ((N * ρ k : ℝ) : ℂ)) ∧
      (∑ k, ρ k ^ p) = 1 ∧ N ^ p = ∑ k, ‖μ k‖ ^ p ∧
      (∑ k, (conj (v k) * (ρ k ^ (p - 1) : ℝ)) * μ k) = (N : ℂ) := by
  let S : ℝ := ∑ k, ‖μ k‖ ^ p
  have ht (k) : 0 < ‖μ k‖ := norm_pos_iff.mpr (hμ k)
  have hS : 0 < S := Finset.sum_pos (fun k _ => Real.rpow_pos_of_pos (ht k) _)
    (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
  let N : ℝ := S ^ p⁻¹
  have hN : 0 < N := Real.rpow_pos_of_pos hS _
  have hNp : N ^ p = S := Real.rpow_inv_rpow hS.le hp.ne'
  let ρ : Fin n → ℝ := fun k => ‖μ k‖ / N
  let v : Fin n → ℂ := fun k => μ k / (‖μ k‖ : ℂ)
  have hρ (k) : 0 < ρ k := div_pos (ht k) hN
  have hv (k) : ‖v k‖ = 1 := by
    simp [v, norm_div, Complex.norm_real, Real.norm_of_nonneg (ht k).le, (ht k).ne']
  have hdecomp (k) : μ k = v k * ((N * ρ k : ℝ) : ℂ) := by
    dsimp [v, ρ]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hN.ne', Complex.ofReal_ne_zero.mpr (ht k).ne']
  have hsum : (∑ k, ρ k ^ p) = 1 := by
    simp only [ρ, Real.div_rpow (norm_nonneg _) hN.le, ← Finset.sum_div, hNp]
    exact div_self hS.ne'
  refine ⟨N, ρ, v, hN, hρ, hv, hdecomp, hsum, hNp, ?_⟩
  calc
    _ = ∑ k, ((N * ρ k ^ p : ℝ) : ℂ) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [hdecomp]
      have hc : conj (v k) * v k = 1 := by
        simpa [hv] using Complex.conj_mul' (v k)
      have hr : ρ k ^ (p - 1) * ρ k = ρ k ^ p := by
        rw [← Real.rpow_add_one (hρ k).ne']
        congr 1
        ring
      calc
        _ = (conj (v k) * v k) * (N : ℂ) * ((ρ k ^ (p - 1) * ρ k : ℝ) : ℂ) := by
          push_cast
          ring
        _ = ((N * ρ k ^ p : ℝ) : ℂ) := by rw [hc, one_mul, hr]; push_cast; rfl
    _ = (N : ℂ) := by rw [← Complex.ofReal_sum, ← Finset.mul_sum, hsum, mul_one]

theorem schur_roots_moment {n : ℕ} (A Q : Matrix (Fin n) (Fin n) ℂ)
    (hQ : Q ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (ht : (Qᴴ * A * Q).IsUpperTriangular) (p : ℝ) :
    (A.charpoly.roots.map (fun w => ‖w‖ ^ p)).sum =
      ∑ k, ‖(Qᴴ * A * Q) k k‖ ^ p := by
  let u : Matrix.unitaryGroup (Fin n) ℂ := ⟨Q, hQ⟩
  have hQQ := (Unitary.mem_iff.mp hQ).1
  have he : (Qᴴ * A * Q).charpoly = A.charpoly := by
    have h := Matrix.charpoly_units_conj' (Unitary.toUnits u) A
    change (Q⁻¹ * A * Q).charpoly = A.charpoly at h
    rwa [Matrix.inv_eq_left_inv hQQ] at h
  rw [← he, Matrix.charpoly_of_isUpperTriangular _ ht,
    Polynomial.roots_prod _ _ (Finset.prod_ne_zero_iff.mpr
      fun k _ => Polynomial.X_sub_C_ne_zero _)]
  simp [List.sum_ofFn]

theorem reciprocal_moment {n : ℕ} (z : Fin n → ℂ) (hz : ∀ j, z j ≠ 0) (p : ℝ) :
    ((Polynomial.derivative (TangZhangOrderMinusTwo.P z)).roots.map
      (fun w => ‖w‖ ^ (-p))).sum =
    ((TangZhangOrderMinusTwo.B (fun j => (z j)⁻¹)).charpoly.roots.map
      (fun μ => ‖μ‖ ^ p)).sum := by
  rw [← TangZhangOrderMinusTwo.roots_derivative z hz, Multiset.map_map]
  simp only [Function.comp_apply, norm_inv, ← Real.rpow_neg_eq_inv_rpow]

def A {n : ℕ} (b : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  H n ((1 / 2 : ℝ) : ℂ) * diagonal b * H n ((1 / 2 : ℝ) : ℂ)

theorem A_charpoly {n : ℕ} (hn : 0 < n) (b : Fin n → ℂ) :
    (A b).charpoly = (TangZhangOrderMinusTwo.B b).charpoly := by
  have hH : H n ((1 / 2 : ℝ) : ℂ) * H n ((1 / 2 : ℝ) : ℂ) = 1 + TangZhangOrderMinusTwo.J n := by
    rw [H_add n hn, show ((1 / 2 : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) = 1 by norm_num,
      H_one n hn]
  unfold A TangZhangOrderMinusTwo.B
  rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hH, Matrix.charpoly_mul_comm]

theorem schur_diagonal_ne_zero {n : ℕ} (hn : 0 < n) (b : Fin n → ℂ)
    (hb : ∀ j, b j ≠ 0) (Q : Matrix (Fin n) (Fin n) ℂ)
    (hQ : Q ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (ht : (Qᴴ * A b * Q).IsUpperTriangular) :
    ∀ k, (Qᴴ * A b * Q) k k ≠ 0 := by
  have hH : (H n ((1 / 2 : ℝ) : ℂ)).det ≠ 0 := by
    apply Matrix.det_ne_zero_of_right_inverse
      (B := H n (-((1 / 2 : ℝ) : ℂ)))
    rw [H_add n hn, add_neg_cancel, H_zero]
  have hD : (diagonal b).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun j _ => hb j)
  have hA : (A b).det ≠ 0 := by simp only [A, Matrix.det_mul]; exact mul_ne_zero (mul_ne_zero hH hD) hH
  have hQQ := Unitary.mem_iff.mp hQ
  have hQ0 : Q.det ≠ 0 := Matrix.det_ne_zero_of_left_inverse hQQ.1
  have hQs0 : Qᴴ.det ≠ 0 := Matrix.det_ne_zero_of_left_inverse hQQ.2
  exact ht.det_ne_zero_iff.mp (by
    simp only [Matrix.det_mul]
    exact mul_ne_zero (mul_ne_zero hQs0 hA) hQ0)

end D5.S3.Zeros.CriticalPoints.SchurMomentNormalization
