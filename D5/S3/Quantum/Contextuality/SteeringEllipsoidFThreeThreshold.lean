/- GID: D5/S3/Quantum/Contextuality/SteeringEllipsoidFThreeThreshold
   generality: I
   mirror-B: D5/B/S3/Quantum/Contextuality/SteeringEllipsoidFThreeThreshold
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The F₃ steering inequality has the sharp ellipsoid-centre threshold two thirds. -/

import D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Kronecker ComplexOrder
open D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
  (pauli blochA blochB corr vlen centre vlen_eq_norm vlen_nonneg)
open D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH
  (vlen_sq normalized_unit trace_pauli_kronecker_eq_corr delta flipped
    flip_purity_identity bob_radius_le delta_le_centre tightState tight_psd tight_readouts
    tight_centre bell bell_trace_real_expansion unit_dot_le)
open D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness (spin)
open D5.S3.QuantumBounds.CHSHWitness renaming TwoQubitMatrix → TwoQubit

namespace D5.S3.Quantum.Contextuality.SteeringEllipsoidFThreeThreshold

/-- Bob's ellipsoid centre, including the pure-Alice marginal convention. -/
def centreB (ρ : TwoQubit) : Fin 3 → ℝ :=
  if vlen (blochA ρ) = 1 then blochB ρ
  else fun j => (blochB ρ j - ∑ i, corr ρ i j * blochA ρ i) / (1 - vlen (blochA ρ) ^ 2)

/-- Three unit Alice settings and an orthonormal Bob frame. -/
def fThreeValues (ρ : TwoQubit) : Set ℝ :=
  {r | ∃ α β : Fin 3 → Fin 3 → ℝ,
    (∀ i, vlen (α i) = 1) ∧
    (∀ i j, β i ⬝ᵥ β j = if i = j then 1 else 0) ∧
    r = ‖∑ i, trace (ρ * (spin (α i) ⊗ₖ spin (β i)))‖ / Real.sqrt 3}

/-- Maximal F₃ steering value. -/
def fThree (ρ : TwoQubit) : ℝ := sSup (fThreeValues ρ)

def claim : Prop :=
  (∀ ρ : TwoQubit, ρ.PosSemidef → trace ρ = 1 →
    fThree ρ ≤ max (Real.sqrt (3 * (1 - vlen (centreB ρ)))) 1) ∧
  (∀ t : ℝ, 0 ≤ t → t < 2 / 3 → ∃ ρ : TwoQubit,
    ρ.PosSemidef ∧ trace ρ = 1 ∧ vlen (centreB ρ) = t ∧ 1 < fThree ρ)

private def swapped (ρ : TwoQubit) : TwoQubit :=
  Matrix.reindex (Equiv.prodComm (Fin 2) (Fin 2)) (Equiv.prodComm (Fin 2) (Fin 2)) ρ

private lemma swap_trace_product (ρ : TwoQubit) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    trace (swapped ρ * (A ⊗ₖ B)) = trace (ρ * (B ⊗ₖ A)) := by
  sorry

private lemma swap_readouts (ρ : TwoQubit) :
    trace (swapped ρ) = trace ρ ∧ blochA (swapped ρ) = blochB ρ ∧
    blochB (swapped ρ) = blochA ρ ∧ corr (swapped ρ) = (corr ρ)ᵀ ∧
    centre (swapped ρ) = centreB ρ ∧ centreB (swapped ρ) = centre ρ := by
  sorry

private lemma frame_energy (T : Matrix (Fin 3) (Fin 3) ℝ)
    (β : Fin 3 → Fin 3 → ℝ)
    (hβ : ∀ i j, β i ⬝ᵥ β j = if i = j then 1 else 0) :
    ∑ i, vlen (T *ᵥ β i) ^ 2 = ∑ i, ∑ j, T i j ^ 2 := by
  sorry

private lemma setting_trace (ρ : TwoQubit) (hρ : ρ.IsHermitian)
    (a b : Fin 3 → ℝ) :
    trace (ρ * (spin a ⊗ₖ spin b)) = ((a ⬝ᵥ (corr ρ *ᵥ b) : ℝ) : ℂ) := by
  sorry

private lemma setting_bound (ρ : TwoQubit) (hρ : ρ.IsHermitian)
    (α β : Fin 3 → Fin 3 → ℝ) (hα : ∀ i, vlen (α i) = 1)
    (hβ : ∀ i j, β i ⬝ᵥ β j = if i = j then 1 else 0) :
    ‖∑ i, trace (ρ * (spin (α i) ⊗ₖ spin (β i)))‖ / Real.sqrt 3 ≤
      Real.sqrt (∑ i, ∑ j, corr ρ i j ^ 2) := by
  sorry

private lemma values_nonempty (ρ : TwoQubit) : (fThreeValues ρ).Nonempty := by
  sorry

private lemma values_bddAbove (ρ : TwoQubit) (hρ : ρ.IsHermitian) :
    BddAbove (fThreeValues ρ) := by
  sorry

private lemma fThree_le_frobenius (ρ : TwoQubit) (hρ : ρ.IsHermitian) :
    fThree ρ ≤ Real.sqrt (∑ i, ∑ j, corr ρ i j ^ 2) := by
  sorry

private lemma summed_flip (ρ : TwoQubit) (hρ : ρ.PosSemidef) (htr : trace ρ = 1) :
    2 * (∑ i, ∑ j, corr ρ i j ^ 2) + vlen (blochB ρ) ^ 2 ≤ 3 + 6 * delta ρ := by
  sorry

private lemma affine_bound (ρ : TwoQubit) (hρ : ρ.PosSemidef) (htr : trace ρ = 1) :
    (∑ i, ∑ j, corr ρ i j ^ 2) ≤ 3 - 3 * vlen (centre ρ) +
      (3 * vlen (centre ρ) - 2) * vlen (blochB ρ) ^ 2 := by
  sorry

private lemma envelope (ρ : TwoQubit) (hρ : ρ.PosSemidef) (htr : trace ρ = 1) :
    (∑ i, ∑ j, corr ρ i j ^ 2) ≤ max (3 * (1 - vlen (centre ρ))) 1 := by
  sorry

private lemma universal_bound (ρ : TwoQubit) (hρ : ρ.PosSemidef) (htr : trace ρ = 1) :
    fThree ρ ≤ max (Real.sqrt (3 * (1 - vlen (centreB ρ)))) 1 := by
  sorry

private lemma balanced_setting (ρ : TwoQubit) (hρ : ρ.IsHermitian) (p q : ℝ)
    (hT : corr ρ = diagonal ![p, -p, q]) (hE : 1 < 2 * p ^ 2 + q ^ 2) :
    1 < fThree ρ := by
  sorry

private lemma threshold_parameters (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t < 2 / 3) :
    0 < 2 - 2 * t - t ^ 2 ∧
    0 ≤ t * (1 - t) / (2 - 2 * t - t ^ 2) ∧
    t * (1 - t) / (2 - 2 * t - t ^ 2) < 1 := by
  sorry

private lemma threshold_energy (t s : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t < 2 / 3)
    (hs : s = t * (1 - t) / (2 - 2 * t - t ^ 2)) :
    1 < 2 * (Real.sqrt (1 + s) * Real.sqrt ((1 - t) * (1 - s))) ^ 2 +
      (1 - t + t * s) ^ 2 := by
  sorry

private lemma threshold_family (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t < 2 / 3) :
    ∃ ρ : TwoQubit, ρ.PosSemidef ∧ trace ρ = 1 ∧
      vlen (centreB ρ) = t ∧ 1 < fThree ρ := by
  sorry

theorem result : claim := ⟨universal_bound, threshold_family⟩

end D5.S3.Quantum.Contextuality.SteeringEllipsoidFThreeThreshold
