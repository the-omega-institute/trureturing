/- GID: D5/S3/Quantum/Measurement/CoherenceFractionIncoherentNonmonotone
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/CoherenceFractionIncoherentNonmonotone
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Measurement/CoherenceFractionIncoherentNonmonotone.claim; result=D5/S3/Quantum/Measurement/CoherenceFractionIncoherentNonmonotone.result; claim=D5/S3/Quantum/Measurement/CoherenceFractionIncoherentNonmonotone.claim
   digest: An incoherent operation increases the quantum coherence fraction. -/

import D5.S3.Quantum.Information.SLDSpectralEnergy
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix Set
open scoped BigOperators ComplexOrder

namespace D5.S3.Quantum.Measurement.CoherenceFractionIncoherentNonmonotone

def IsIncoherentOperation {d m : ℕ}
    (k : Fin m → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  (∑ i, (k i)ᴴ * k i = 1) ∧
    ∀ i ρ, ρ.IsDiag → (k i * ρ * (k i)ᴴ).IsDiag

noncomputable def coherenceFraction {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  sSup {r : ℝ | ∃ z : Fin d → ℂ, (∀ j, ‖z j‖ = 1) ∧
    r = (star z ⬝ᵥ (ρ *ᵥ z)).re / (d : ℝ)}

def claim : Prop := ∀ (d m : ℕ) (ρ : Matrix (Fin d) (Fin d) ℂ)
    (k : Fin m → Matrix (Fin d) (Fin d) ℂ),
    D5.S3.Quantum.Information.SLDSpectralEnergy.IsDensity ρ →
    IsIncoherentOperation k →
    coherenceFraction (∑ i, k i * ρ * (k i)ᴴ) ≤ coherenceFraction ρ

private def b : Matrix (Fin 4) (Fin 2) ℂ :=
  ![![1, 0], ![0, 1], ![(3 : ℂ) / 5, (4 : ℂ) / 5],
    ![(3 : ℂ) / 5, (4 : ℂ) * Complex.I / 5]]

private def p : Matrix (Fin 4) (Fin 4) ℂ :=
  ![ ![(475 : ℂ) / 721, (-100 : ℂ) / 721 - (100 : ℂ) * Complex.I / 721,
      (205 : ℂ) / 721 - (80 : ℂ) * Complex.I / 721,
      (205 : ℂ) / 721 + (80 : ℂ) * Complex.I / 721],
    ![(-100 : ℂ) / 721 + (100 : ℂ) * Complex.I / 721, (1075 : ℂ) / 2163,
      (680 : ℂ) / 2163 + (60 : ℂ) * Complex.I / 721,
      (-60 : ℂ) / 721 - (680 : ℂ) * Complex.I / 2163],
    ![(205 : ℂ) / 721 + (80 : ℂ) * Complex.I / 721,
      (680 : ℂ) / 2163 - (60 : ℂ) * Complex.I / 721, (913 : ℂ) / 2163,
      (75 : ℂ) / 721 - (400 : ℂ) * Complex.I / 2163],
    ![(205 : ℂ) / 721 - (80 : ℂ) * Complex.I / 721,
      (-60 : ℂ) / 721 + (680 : ℂ) * Complex.I / 2163,
      (75 : ℂ) / 721 + (400 : ℂ) * Complex.I / 2163, (913 : ℂ) / 2163]]

private def rho : Matrix (Fin 4) (Fin 4) ℂ :=
  ![ ![(475 : ℂ) / 1442, (-50 : ℂ) / 721 - (50 : ℂ) * Complex.I / 721,
      (205 : ℂ) / 1442 - (40 : ℂ) * Complex.I / 721,
      (205 : ℂ) / 1442 + (40 : ℂ) * Complex.I / 721],
    ![(-50 : ℂ) / 721 + (50 : ℂ) * Complex.I / 721, (1075 : ℂ) / 4326,
      (340 : ℂ) / 2163 + (30 : ℂ) * Complex.I / 721,
      (-30 : ℂ) / 721 - (340 : ℂ) * Complex.I / 2163],
    ![(205 : ℂ) / 1442 + (40 : ℂ) * Complex.I / 721,
      (340 : ℂ) / 2163 - (30 : ℂ) * Complex.I / 721, (913 : ℂ) / 4326,
      (75 : ℂ) / 1442 - (200 : ℂ) * Complex.I / 2163],
    ![(205 : ℂ) / 1442 - (40 : ℂ) * Complex.I / 721,
      (-30 : ℂ) / 721 + (340 : ℂ) * Complex.I / 2163,
      (75 : ℂ) / 1442 + (200 : ℂ) * Complex.I / 2163, (913 : ℂ) / 4326]]

private def k : Fin 2 → Matrix (Fin 4) (Fin 4) ℂ
  | 0 => Matrix.diagonal ![1, 0, (3 : ℂ) / 5, (3 : ℂ) / 5]
  | 1 => Matrix.diagonal ![0, 1, (4 : ℂ) / 5, (-4 : ℂ) * Complex.I / 5]

private def phi (ρ : Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ∑ i, k i * ρ * (k i)ᴴ

private def ones : Fin 4 → ℂ := fun _ => 1

private lemma p_star : pᴴ = p := by
  ext i j
  change star (p j i) = p i j
  fin_cases i <;> fin_cases j <;> simp [p, Complex.star_def] <;> ring

private lemma p_square : p * p = p := by
  ext i j
  change (∑ t, p i t * p t j) = p i j
  fin_cases i <;> fin_cases j <;>
    simp [p, Fin.sum_univ_succ] <;> ring_nf <;>
      try rw [Complex.I_sq] <;> norm_num <;> ring

private lemma p_trace : trace p = 2 := by
  change ∑ i, p i i = 2
  simp [p, Matrix.diag, Fin.sum_univ_succ] <;> norm_num <;> ring

private lemma p_range : p * b = b := by
  ext i j
  change (∑ t, p i t * b t j) = b i j
  fin_cases i <;> fin_cases j <;>
    simp [p, b, Fin.sum_univ_succ] <;> ring_nf <;>
      try rw [Complex.I_sq] <;> norm_num <;> ring

private lemma p_pos : p.PosSemidef := by
  have h := Matrix.PosSemidef.mul_mul_conjTranspose_same
    (Matrix.PosSemidef.one : (1 : Matrix (Fin 4) (Fin 4) ℂ).PosSemidef) p
  simpa [p_star, p_square] using h

private lemma rho_density :
    D5.S3.Quantum.Information.SLDSpectralEnergy.IsDensity rho := by
  have hs (i j : Fin 4) : ((1 / 2 : ℝ) • p) i j = (1 / 2 : ℂ) * p i j := by
    change (1 / 2 : ℝ) • p i j = _
    rw [Algebra.smul_def]
    norm_num
  have hr : rho = (1 / 2 : ℝ) • p := by
    ext i j
    rw [hs]
    fin_cases i <;> fin_cases j <;>
      simp [rho, p, Complex.ext_iff, Complex.I_sq, div_eq_mul_inv] <;>
      norm_num <;> ring
  rw [hr]
  constructor
  · simpa using p_pos.smul (by norm_num : (0 : ℝ) ≤ 1 / 2)
  · simp [Matrix.trace_smul, p_trace]

private lemma k_incoherent : IsIncoherentOperation k := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [k, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
        Fin.sum_univ_two, map_inv₀, map_ofNat, Complex.I_sq] <;>
      norm_num [Complex.ext_iff, Complex.I_sq, div_eq_mul_inv] <;> ring
  · intro i σ hσ
    rw [← hσ.diagonal_diag]
    fin_cases i <;>
      simp [k, Matrix.diagonal_mul_diagonal, Matrix.diagonal_conjTranspose]

private lemma coherence_bddAbove (σ : Matrix (Fin 4) (Fin 4) ℂ) :
    BddAbove {r : ℝ | ∃ z : Fin 4 → ℂ, (∀ j, ‖z j‖ = 1) ∧
      r = (star z ⬝ᵥ (σ *ᵥ z)).re / (4 : ℝ)} := by sorry

private def q : Matrix (Fin 4) (Fin 4) ℂ :=
  ![ ![(1 / 2 : ℂ) * (475 / 721), 0,
      (3 / 10 : ℂ) * (205 / 721 - (80 : ℂ) * Complex.I / 721),
      (3 / 10 : ℂ) * (205 / 721 + (80 : ℂ) * Complex.I / 721)],
    ![0, (1 / 2 : ℂ) * (1075 / 2163),
      (2 / 5 : ℂ) * (680 / 2163 + (60 : ℂ) * Complex.I / 721),
      (2 / 5 : ℂ) * Complex.I * (-60 / 721 - (680 : ℂ) * Complex.I / 2163)],
    ![(3 / 10 : ℂ) * (205 / 721 + (80 : ℂ) * Complex.I / 721),
      (2 / 5 : ℂ) * (680 / 2163 - (60 : ℂ) * Complex.I / 721),
      (1 / 2 : ℂ) * (913 / 2163),
      (1 / 2 : ℂ) * ((9 / 25 : ℂ) + (16 / 25 : ℂ) * Complex.I) *
        (75 / 721 - (400 : ℂ) * Complex.I / 2163)],
    ![(3 / 10 : ℂ) * (205 / 721 - (80 : ℂ) * Complex.I / 721),
      -(2 / 5 : ℂ) * Complex.I * (-60 / 721 + (680 : ℂ) * Complex.I / 2163),
      (1 / 2 : ℂ) * ((9 / 25 : ℂ) - (16 / 25 : ℂ) * Complex.I) *
        (75 / 721 + (400 : ℂ) * Complex.I / 2163),
      (1 / 2 : ℂ) * (913 / 2163)]]

private lemma diag_sandwich (a b : Fin 4 → ℂ) (m : Matrix (Fin 4) (Fin 4) ℂ)
    (i j : Fin 4) :
    (Matrix.diagonal a * m * Matrix.diagonal b) i j = a i * m i j * b j := by
  simp [Matrix.mul_apply, Matrix.diagonal, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000 in
private lemma phi_rho : phi rho = q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [phi, Fin.sum_univ_two, Matrix.add_apply, k,
      Matrix.diagonal_conjTranspose] <;>
    simp only [diag_sandwich] <;>
    simp [q, rho, Complex.ext_iff, Complex.I_sq, div_eq_mul_inv] <;>
    norm_num <;> ring

private lemma output_at_ones :
    (star ones ⬝ᵥ (phi rho *ᵥ ones)).re / (4 : ℝ) = 1 / 2 := by
  rw [phi_rho]
  norm_num [q, ones, Matrix.mul_apply, Matrix.mulVec, Matrix.vecMul,
    Matrix.smul_apply, Matrix.diagonal, Matrix.star_eq_conjTranspose, Pi.star_apply, dotProduct,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.vecHead, Matrix.vecTail,
    Matrix.cons_val_fin_one, Matrix.cons_val_two, Fin.reduceFinMk, Matrix.of_apply,
    Pi.smul_apply, smul_eq_mul, Algebra.smul_def,
    Fin.sum_univ_succ, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
    map_inv₀, map_ofNat, Complex.ext_iff, Complex.I_sq, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.smul_re,
    Complex.ofReal_re, Complex.ofReal_im, div_eq_mul_inv] <;>
      simp_rw [Matrix.smul_apply, Algebra.smul_def] <;>
      norm_num <;> ring_nf <;> norm_num

private lemma input_bound (z : Fin 4 → ℂ) (hz : ∀ j, ‖z j‖ = 1) :
    (star z ⬝ᵥ (rho *ᵥ z)).re / (4 : ℝ) ≤ 1 / 2 - 1 / 200 := by sorry

private lemma output_lower : 1 / 2 ≤ coherenceFraction (phi rho) := by sorry

private lemma input_upper : coherenceFraction rho ≤ 1 / 2 - 1 / 200 := by sorry

theorem result : ¬ claim := by
  intro h
  have hm := h 4 2 rho k rho_density k_incoherent
  have hlt : coherenceFraction (phi rho) > coherenceFraction rho :=
    lt_of_le_of_lt input_upper ?_
  · exact (not_lt_of_ge hm) hlt
  · exact lt_of_lt_of_le (by norm_num : (1 / 2 - 1 / 200 : ℝ) < 1 / 2) output_lower

end D5.S3.Quantum.Measurement.CoherenceFractionIncoherentNonmonotone
