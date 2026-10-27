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

private def rho : Matrix (Fin 4) (Fin 4) ℂ := (1 / 2 : ℂ) • p

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

private lemma p_pos : p.PosSemidef := by sorry

private lemma rho_density :
    D5.S3.Quantum.Information.SLDSpectralEnergy.IsDensity rho := by sorry

private lemma k_incoherent : IsIncoherentOperation k := by sorry

private lemma coherence_bddAbove (σ : Matrix (Fin 4) (Fin 4) ℂ) :
    BddAbove {r : ℝ | ∃ z : Fin 4 → ℂ, (∀ j, ‖z j‖ = 1) ∧
      r = (star z ⬝ᵥ (σ *ᵥ z)).re / (4 : ℝ)} := by sorry

private lemma output_at_ones :
    (star ones ⬝ᵥ (phi rho *ᵥ ones)).re / (4 : ℝ) = 1 / 2 := by sorry

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
