/- GID: D5/S3/Quantum/Matrix/UnitaryScalingLandscapeRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/UnitaryScalingLandscapeRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Matrix/UnitaryScalingLandscapeRefutation.claim; result=D5/S3/Quantum/Matrix/UnitaryScalingLandscapeRefutation.result; claim=D5/S3/Quantum/Matrix/UnitaryScalingLandscapeRefutation.claim
   digest: A unitary matrix of order three has a nonglobal local scaling minimum. -/

import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! The sum of the entries of a diagonally scaled unitary matrix can have a
nonglobal local maximum in modulus, giving a nonglobal local minimum of its landscape. -/

noncomputable section

open Matrix Finset
open scoped Topology

namespace D5.S3.Quantum.Matrix.UnitaryScalingLandscapeRefutation

def scalingSum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (x : (Fin n → ℝ) × (Fin n → ℝ)) : ℂ :=
  ∑ j, ∑ k, Complex.exp (((x.1 j + x.2 k : ℝ) : ℂ) * Complex.I) * A j k

def landscape {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (x : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  (n : ℝ) ^ 2 - ‖scalingSum A x‖ ^ 2

def claim : Prop :=
  ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ), A ∈ Matrix.unitaryGroup (Fin n) ℂ →
    ∀ x, IsLocalMin (landscape A) x → ∀ y, landscape A x ≤ landscape A y

private def phase (t : ℝ) : ℂ := Complex.exp ((t : ℂ) * Complex.I)

private theorem phase_norm (t : ℝ) : ‖phase t‖ = 1 := by
  simp [phase, Complex.norm_exp]

private theorem phase_add (s t : ℝ) : phase (s + t) = phase s * phase t := by
  simp only [phase, Complex.ofReal_add, add_mul, Complex.exp_add]

private def witnessMatrix : Matrix (Fin 3) (Fin 3) ℂ :=
  !![-2 / 34, 24 / 34, 24 / 34;
     24 / 34, (1 + 17 * Complex.I) / 34, (1 - 17 * Complex.I) / 34;
     24 / 34, (1 - 17 * Complex.I) / 34, (1 + 17 * Complex.I) / 34]

private theorem witness_unitary : witnessMatrix ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Matrix.star_apply, witnessMatrix, Fin.sum_univ_succ,
      Complex.ext_iff, Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]

private theorem scaling_zero : scalingSum witnessMatrix 0 = (49 / 17 : ℂ) := by
  norm_num [scalingSum, witnessMatrix, Fin.sum_univ_succ]
  ring

private theorem landscape_zero : landscape witnessMatrix 0 = 200 / 289 := by
  rw [landscape, scaling_zero]
  norm_num

private def rowSum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (ρ : Fin n → ℝ)
    (j : Fin n) : ℂ := ∑ k, A j k * phase (ρ k)

private theorem scaling_rows {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (x : (Fin n → ℝ) × (Fin n → ℝ)) :
    scalingSum A x = ∑ j, phase (x.1 j) * rowSum A x.2 j := by
  unfold scalingSum rowSum
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [← phase, phase_add]
  ring

private theorem scaling_triangle {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (x : (Fin n → ℝ) × (Fin n → ℝ)) :
    ‖scalingSum A x‖ ≤ ∑ j, ‖rowSum A x.2 j‖ := by
  rw [scaling_rows]
  calc
    ‖∑ j, phase (x.1 j) * rowSum A x.2 j‖ ≤
        ∑ j, ‖phase (x.1 j) * rowSum A x.2 j‖ := norm_sum_le _ _
    _ = ∑ j, ‖rowSum A x.2 j‖ := by simp only [norm_mul, phase_norm, one_mul]

private theorem phase_align (z : ℂ) : phase (-Complex.arg z) * z = (‖z‖ : ℂ) := by
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I z]
  rw [mul_left_comm, ← phase, ← phase_add]
  simp [phase]

private theorem scaling_aligned {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (ρ : Fin n → ℝ) :
    ‖scalingSum A (fun j => -Complex.arg (rowSum A ρ j), ρ)‖ =
      ∑ j, ‖rowSum A ρ j‖ := by
  rw [scaling_rows]
  simp only [phase_align]
  rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)]

private theorem norm_affine_phase_sq (a b u : ℝ) :
    ‖(a : ℂ) + (b : ℂ) * phase u‖ ^ 2 =
      (a + b) ^ 2 - 2 * a * b * (1 - Real.cos u) := by
  rw [Complex.sq_norm, Complex.normSq_add, Complex.normSq_mul,
    Complex.normSq_ofReal, Complex.normSq_ofReal, Complex.normSq_eq_norm_sq, phase_norm]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, map_mul,
    Complex.conj_ofReal, Complex.conj_re, phase, Complex.exp_ofReal_mul_I_re,
    zero_mul, sub_zero]
  ring

private theorem central_radius_bound (b h R : ℝ) (hb : 23 / 24 ≤ b)
    (hh : 0 ≤ h) (hR : 0 ≤ R)
    (hsq : R ^ 2 = (24 * b - 1) ^ 2 + 48 * b * h) :
    R ≤ 24 * b - 1 + 12 * b * h / 11 := by
  have hb0 : 0 ≤ b := by linarith
  have hT : 22 ≤ 24 * b - 1 := by linarith
  have hbase : 24 * b - 1 ≤ R := by
    nlinarith [mul_nonneg hb0 hh]
  have hprod : (R - (24 * b - 1)) * (R + (24 * b - 1)) = 48 * b * h := by
    nlinarith [hsq]
  have hmul := mul_le_mul_of_nonneg_left (show 44 ≤ R + (24 * b - 1) by linarith)
    (show 0 ≤ R - (24 * b - 1) by linarith)
  nlinarith [hprod, hmul]

private theorem side_radius_bound (B h R : ℝ) (hB0 : 0 ≤ B) (hB2 : B ≤ 2)
    (hh : 0 ≤ h) (hR : 0 ≤ R)
    (hsq : R ^ 2 = (12 + B) ^ 2 - 24 * B * h) :
    R ≤ 12 + B - 6 * B * h / 7 := by
  have hbase : R ≤ 12 + B := by nlinarith [mul_nonneg hB0 hh]
  have hprod : (12 + B - R) * (12 + B + R) = 24 * B * h := by
    nlinarith [hsq]
  have hmul := mul_le_mul_of_nonneg_left (show 12 + B + R ≤ 28 by linarith)
    (show 0 ≤ 12 + B - R by linarith)
  nlinarith [hprod, hmul]

private theorem radial_certificate (u v : ℝ) (hv : |v| < 1 / 100) :
    ‖(-1 : ℂ) + (24 * Real.cos v : ℝ) * phase u‖ +
      ‖(12 : ℂ) + ((Real.cos v - 17 * Real.sin v : ℝ) : ℂ) * phase u‖ +
      ‖(12 : ℂ) + ((Real.cos v + 17 * Real.sin v : ℝ) : ℂ) * phase u‖ ≤ 49 := by
  have ht : |Real.sin v| ≤ 1 / 100 := (Real.abs_sin_le_abs).trans hv.le
  have hv2 : v ^ 2 ≤ (1 / 100 : ℝ) ^ 2 := by
    have := abs_le.mp hv.le
    nlinarith
  have hb : 23 / 24 ≤ Real.cos v := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := v)]
  have hb1 := Real.cos_le_one v
  have hh : 0 ≤ 1 - Real.cos u := sub_nonneg.mpr (Real.cos_le_one u)
  have hm0 : 0 ≤ Real.cos v - 17 * Real.sin v := by
    have := abs_le.mp ht
    linarith
  have hp0 : 0 ≤ Real.cos v + 17 * Real.sin v := by
    have := abs_le.mp ht
    linarith
  have hm2 : Real.cos v - 17 * Real.sin v ≤ 2 := by
    have := abs_le.mp ht
    linarith
  have hp2 : Real.cos v + 17 * Real.sin v ≤ 2 := by
    have := abs_le.mp ht
    linarith
  have h0 := norm_affine_phase_sq (-1) (24 * Real.cos v) u
  have hm := norm_affine_phase_sq 12 (Real.cos v - 17 * Real.sin v) u
  have hp := norm_affine_phase_sq 12 (Real.cos v + 17 * Real.sin v) u
  have e0 := central_radius_bound (Real.cos v) (1 - Real.cos u)
    ‖(-1 : ℂ) + (24 * Real.cos v : ℝ) * phase u‖ hb hh (norm_nonneg _)
    (by norm_num only [Complex.ofReal_neg, Complex.ofReal_one] at h0; nlinarith [h0])
  have em := side_radius_bound (Real.cos v - 17 * Real.sin v) (1 - Real.cos u)
    ‖(12 : ℂ) + ((Real.cos v - 17 * Real.sin v : ℝ) : ℂ) * phase u‖
    hm0 hm2 hh (norm_nonneg _) (by norm_num only [Complex.ofReal_ofNat] at hm; linarith)
  have ep := side_radius_bound (Real.cos v + 17 * Real.sin v) (1 - Real.cos u)
    ‖(12 : ℂ) + ((Real.cos v + 17 * Real.sin v : ℝ) : ℂ) * phase u‖
    hp0 hp2 hh (norm_nonneg _) (by norm_num only [Complex.ofReal_ofNat] at hp; linarith)
  have hb0 : 0 ≤ Real.cos v := by linarith
  nlinarith [mul_nonneg hb0 hh]

private def reducedRows (u v : ℝ) : Fin 3 → ℂ :=
  ![(-1 : ℂ) + ((24 * Real.cos v : ℝ) : ℂ) * phase u,
    (12 : ℂ) + ((Real.cos v - 17 * Real.sin v : ℝ) : ℂ) * phase u,
    (12 : ℂ) + ((Real.cos v + 17 * Real.sin v : ℝ) : ℂ) * phase u]

private theorem row_reduction (ρ : Fin 3 → ℝ) (j : Fin 3) :
    rowSum witnessMatrix ρ j = phase (ρ 0) / 17 *
      reducedRows ((ρ 1 + ρ 2) / 2 - ρ 0) ((ρ 1 - ρ 2) / 2) j := by
  let u := (ρ 1 + ρ 2) / 2 - ρ 0
  let v := (ρ 1 - ρ 2) / 2
  have h1 : phase (ρ 1) = phase (ρ 0) * phase u * phase v := by
    rw [← phase_add, ← phase_add]
    congr 1
    dsimp [u, v]
    ring
  have h2 : phase (ρ 2) = phase (ρ 0) * phase u * phase (-v) := by
    rw [← phase_add, ← phase_add]
    congr 1
    dsimp [u, v]
    ring
  have hv : phase v = (Real.cos v : ℂ) + (Real.sin v : ℂ) * Complex.I :=
    Complex.exp_ofReal_mul_I v
  have hnv : phase (-v) = (Real.cos v : ℂ) - (Real.sin v : ℂ) * Complex.I := by
    rw [phase, Complex.exp_ofReal_mul_I]
    simp only [Real.cos_neg, Real.sin_neg,
      Complex.ofReal_neg, neg_mul, sub_eq_add_neg]
  change rowSum witnessMatrix ρ j = phase (ρ 0) / 17 * reducedRows u v j
  fin_cases j <;>
    simp [rowSum, witnessMatrix, reducedRows, Fin.sum_univ_succ, h1, h2, hv, hnv,
      Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul] <;>
    ring_nf <;> simp only [Complex.I_sq] <;> ring

private theorem column_norm_bound (ρ : Fin 3 → ℝ) (hρ : |ρ 1 - ρ 2| < 1 / 50) :
    ∑ j, ‖rowSum witnessMatrix ρ j‖ ≤ 49 / 17 := by
  let u := (ρ 1 + ρ 2) / 2 - ρ 0
  let v := (ρ 1 - ρ 2) / 2
  have hv : |v| < 1 / 100 := by
    dsimp [v]
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hred : ∑ j, ‖reducedRows u v j‖ ≤ 49 := by
    simpa [reducedRows, Fin.sum_univ_succ, add_assoc] using radial_certificate u v hv
  calc
    ∑ j, ‖rowSum witnessMatrix ρ j‖ = ∑ j, (1 / 17 : ℝ) * ‖reducedRows u v j‖ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [row_reduction, norm_mul, norm_div, phase_norm]
      norm_num [u, v]
    _ = (1 / 17 : ℝ) * ∑ j, ‖reducedRows u v j‖ := (Finset.mul_sum ..).symm
    _ ≤ 49 / 17 := by linarith

private theorem witness_local_min : IsLocalMin (landscape witnessMatrix) 0 := by
  have hc : Continuous (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => |p.2 1 - p.2 2|) := by
    fun_prop
  have hU : {p : (Fin 3 → ℝ) × (Fin 3 → ℝ) | |p.2 1 - p.2 2| < 1 / 50} ∈
      𝓝 (0 : (Fin 3 → ℝ) × (Fin 3 → ℝ)) :=
    (isOpen_lt hc continuous_const).mem_nhds (by norm_num)
  filter_upwards [hU] with p hp
  have hnorm := (scaling_triangle witnessMatrix p).trans (column_norm_bound p.2 hp)
  rw [landscape_zero, landscape]
  have hn := norm_nonneg (scalingSum witnessMatrix p)
  norm_num only [Nat.cast_ofNat]
  nlinarith

private def comparisonColumns : Fin 3 → ℝ := ![0, 2 * Real.pi / 3, Real.pi / 3]

private theorem comparison_squares (j : Fin 3) :
    ‖rowSum witnessMatrix comparisonColumns j‖ ^ 2 =
      ![(433 / 289 : ℝ), 217 / 289 - Real.sqrt 3 / 34,
        217 / 289 + Real.sqrt 3 / 34] j := by
  have hu : (comparisonColumns 1 + comparisonColumns 2) / 2 - comparisonColumns 0 =
      Real.pi / 2 := by norm_num [comparisonColumns]; ring
  have hv : (comparisonColumns 1 - comparisonColumns 2) / 2 = Real.pi / 6 := by
    norm_num [comparisonColumns]
    ring
  rw [row_reduction, hu, hv, norm_mul, norm_div, phase_norm]
  norm_num only [mul_pow, div_pow, one_pow]
  have h0 := norm_affine_phase_sq (-1) (24 * Real.cos (Real.pi / 6)) (Real.pi / 2)
  have hm := norm_affine_phase_sq 12
    (Real.cos (Real.pi / 6) - 17 * Real.sin (Real.pi / 6)) (Real.pi / 2)
  have hp := norm_affine_phase_sq 12
    (Real.cos (Real.pi / 6) + 17 * Real.sin (Real.pi / 6)) (Real.pi / 2)
  norm_num only [Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_ofNat,
    Real.cos_pi_div_two, Real.cos_pi_div_six, Real.sin_pi_div_six] at h0 hm hp
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  fin_cases j <;>
    norm_num [reducedRows, Real.cos_pi_div_six, Real.sin_pi_div_six] at h0 hm hp ⊢ <;>
    nlinarith

private theorem comparison_larger : 49 / 17 < ∑ j, ‖rowSum witnessMatrix comparisonColumns j‖ := by
  have hs : (3 / 2 : ℝ) ≤ Real.sqrt 3 := Real.le_sqrt_of_sq_le (by norm_num)
  have hs2 : Real.sqrt 3 ≤ 2 := (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : (6 / 5 : ℝ) ≤ ‖rowSum witnessMatrix comparisonColumns 0‖ := by
    have := comparison_squares 0
    norm_num only [Matrix.cons_val_zero] at this
    nlinarith [norm_nonneg (rowSum witnessMatrix comparisonColumns 0)]
  have hm : (4 / 5 : ℝ) ≤ ‖rowSum witnessMatrix comparisonColumns 1‖ := by
    have := comparison_squares 1
    norm_num at this
    nlinarith [norm_nonneg (rowSum witnessMatrix comparisonColumns 1)]
  have hp : (8 / 9 : ℝ) ≤ ‖rowSum witnessMatrix comparisonColumns 2‖ := by
    have := comparison_squares 2
    norm_num at this
    nlinarith [norm_nonneg (rowSum witnessMatrix comparisonColumns 2)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change 49 / 17 < ‖rowSum witnessMatrix comparisonColumns 0‖ +
    (‖rowSum witnessMatrix comparisonColumns 1‖ + ‖rowSum witnessMatrix comparisonColumns 2‖)
  linarith

theorem result : ¬ claim := by
  intro h
  have hglobal := h 3 witnessMatrix witness_unitary 0 witness_local_min
    (fun j => -Complex.arg (rowSum witnessMatrix comparisonColumns j), comparisonColumns)
  rw [landscape_zero, landscape, scaling_aligned] at hglobal
  have hs := comparison_larger
  norm_num only [Nat.cast_ofNat] at hglobal
  nlinarith

end D5.S3.Quantum.Matrix.UnitaryScalingLandscapeRefutation
