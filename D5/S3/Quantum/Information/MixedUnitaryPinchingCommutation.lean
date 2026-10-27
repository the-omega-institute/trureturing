/- GID: D5/S3/Quantum/Information/MixedUnitaryPinchingCommutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/MixedUnitaryPinchingCommutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Non-isotropic mixed-unitary qubit channels fail to commute with marginal pinching. -/

import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder Kronecker
open D5.S3.Quantum.FiniteDimensional (QubitMatrix qubitX qubitZ)
open D5.S3.Quantum.Information.ActualPureQubitCostInfimum (bloch blochMatrix blochLinear)
open D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight)
open D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness (sigma spin)

namespace D5.S3.Quantum.Information.MixedUnitaryPinchingCommutation

/-- A finite convex combination of unitary conjugations, on every complex matrix. -/
def IsMixedUnitary (φ : QubitMatrix → QubitMatrix) : Prop :=
  ∃ (k : ℕ) (p : Fin k → ℝ) (u : Fin k → QubitMatrix),
    (∀ j, 0 ≤ p j) ∧ (∑ j, p j = 1) ∧
    (∀ j, u j ∈ unitaryGroup (Fin 2) ℂ) ∧
    ∀ a, φ a = ∑ j, (p j : ℂ) • (u j * a * star (u j))

/-- The source's isotropic channels, extended linearly from states to all matrices.
The antiunitary action on states is `a ↦ u * aᵀ * star u`. -/
def IsIsotropic (φ : QubitMatrix → QubitMatrix) : Prop :=
  ∃ γ ∈ Set.Icc (0 : ℝ) 1, ∃ u ∈ unitaryGroup (Fin 2) ℂ,
    (∀ a, φ a = ((1 - γ : ℝ) : ℂ) • (u * a * star u) +
      (γ : ℂ) • (a.trace / 2) • 1) ∨
    (∀ a, φ a = ((1 - γ : ℝ) : ℂ) • (u * aᵀ * star u) +
      (γ : ℂ) • (a.trace / 2) • 1)

/-- The tensor extension `φ ⊗ id`, acting on each block indexed by the second qubit. -/
def localMap (φ : QubitMatrix → QubitMatrix)
    (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun a c => φ (fun i j => ρ (i, a.2) (j, c.2)) a.1 c.1

/-- The marginal on the first qubit is the partial trace over the second qubit. -/
def marginalA (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : QubitMatrix :=
  partialTraceRight ρ

/-- A Hermitian qubit matrix with two distinct eigenvalues. -/
def IsNondegenerate (a : QubitMatrix) : Prop :=
  ∃ h : a.IsHermitian, Function.Injective h.eigenvalues

/-- Pinching in a spectral basis of the first marginal, by its rank-one eigenprojectors.
The value outside the Hermitian-marginal domain is an arbitrary total extension. -/
def pinchA (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := by
  classical
  exact if h : (marginalA ρ).IsHermitian then
    ∑ i : Fin 2,
      let p : QubitMatrix := fun a c =>
        h.eigenvectorBasis i a * star (h.eigenvectorBasis i c)
      (p ⊗ₖ (1 : QubitMatrix)) * ρ * (p ⊗ₖ (1 : QubitMatrix))
  else ρ

private def blochOperator (φ : QubitMatrix → QubitMatrix) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => (trace (sigma i.succ * φ (sigma j.succ))).re / 2

private def witness (n x : Fin 3 → ℝ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (1 / 4 : ℂ) • ((1 : QubitMatrix) ⊗ₖ (1 : QubitMatrix) +
    (1 / 2 : ℂ) • (spin n ⊗ₖ (1 : QubitMatrix)) +
    (1 / 4 : ℂ) • (spin x ⊗ₖ qubitZ))

private lemma mixed_channel_data (φ : QubitMatrix → QubitMatrix) (hφ : IsMixedUnitary φ) :
    (∃ f : QubitMatrix →ₗ[ℂ] QubitMatrix, ∀ a, φ a = f a) ∧
    φ 1 = 1 ∧ (∀ a, (φ a).trace = a.trace) ∧
    (∀ a, a.IsHermitian → (φ a).IsHermitian) ∧
    ∀ v : Fin 3 → ℝ, φ (spin v) = spin (blochOperator φ *ᵥ v) := by
  sorry

private lemma scalar_gram_isotropic (φ : QubitMatrix → QubitMatrix)
    (hφ : IsMixedUnitary φ)
    (hq : ∃ c : ℝ, (blochOperator φ)ᵀ * blochOperator φ = c • 1) :
    IsIsotropic φ := by
  sorry

private lemma orthogonal_probe (t : Matrix (Fin 3) (Fin 3) ℝ)
    (ht : ¬ ∃ c : ℝ, tᵀ * t = c • 1) :
    ∃ n x : Fin 3 → ℝ, n ⬝ᵥ n = 1 ∧ x ⬝ᵥ x = 1 ∧ n ⬝ᵥ x = 0 ∧
      (t *ᵥ n) ⬝ᵥ (t *ᵥ x) ≠ 0 := by
  sorry

private lemma pinching_formula
    (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (v : Fin 3 → ℝ)
    (hm : marginalA ρ = blochMatrix 1 (WithLp.toLp 2 v)) (hv : v ≠ 0) :
    pinchA ρ = (1 / 2 : ℂ) •
      (ρ + (((v ⬝ᵥ v)⁻¹ : ℝ) : ℂ) •
        ((spin v ⊗ₖ (1 : QubitMatrix)) * ρ * (spin v ⊗ₖ (1 : QubitMatrix)))) := by
  sorry

private lemma witness_density (n x : Fin 3 → ℝ)
    (hn : n ⬝ᵥ n = 1) (hx : x ⬝ᵥ x = 1) (hnx : n ⬝ᵥ x = 0) :
    (witness n x).PosSemidef ∧ (witness n x).trace = 1 := by
  sorry

private lemma witness_marginal (n x : Fin 3 → ℝ) :
    marginalA (witness n x) = blochMatrix 1 (WithLp.toLp 2 ((1 / 2 : ℝ) • n)) := by
  sorry

private lemma mapped_marginal (φ : QubitMatrix → QubitMatrix) (hφ : IsMixedUnitary φ)
    (n x : Fin 3 → ℝ) :
    marginalA (localMap φ (witness n x)) = φ (marginalA (witness n x)) ∧
    φ (marginalA (witness n x)) =
      blochMatrix 1 (WithLp.toLp 2 ((1 / 2 : ℝ) • (blochOperator φ *ᵥ n))) := by
  sorry

private lemma bloch_nondegenerate (v : Fin 3 → ℝ) (hv : v ≠ 0) :
    IsNondegenerate (blochMatrix 1 (WithLp.toLp 2 v)) := by
  sorry

private lemma commutator_identity (φ : QubitMatrix → QubitMatrix) (hφ : IsMixedUnitary φ)
    (n x : Fin 3 → ℝ) (hn : n ⬝ᵥ n = 1) (hnx : n ⬝ᵥ x = 0)
    (htn : blochOperator φ *ᵥ n ≠ 0) :
    pinchA (localMap φ (witness n x)) - localMap φ (pinchA (witness n x)) =
      ((((blochOperator φ *ᵥ n) ⬝ᵥ (blochOperator φ *ᵥ x) /
        ((blochOperator φ *ᵥ n) ⬝ᵥ (blochOperator φ *ᵥ n)) : ℝ) : ℂ) / 16) •
        (spin (blochOperator φ *ᵥ n) ⊗ₖ qubitZ) := by
  have hpin := pinching_formula (witness n x) ((1 / 2 : ℝ) • n)
    (witness_marginal n x)
  have hout := mapped_marginal φ hφ n x
  have hpinout := pinching_formula (localMap φ (witness n x))
    ((1 / 2 : ℝ) • (blochOperator φ *ᵥ n)) (hout.1.trans hout.2)
  sorry

private lemma commutator_nonzero (a b : Fin 3 → ℝ) (hab : a ⬝ᵥ b ≠ 0) :
    ((((a ⬝ᵥ b) / (a ⬝ᵥ a) : ℝ) : ℂ) / 16) • (spin a ⊗ₖ qubitZ) ≠ 0 := by
  sorry

/-- Every non-isotropic mixed-unitary qubit channel fails to commute with marginal pinching
on a two-qubit density matrix whose input and output marginals are nondegenerate. -/
theorem result (φ : QubitMatrix → QubitMatrix) (hφ : IsMixedUnitary φ)
    (hi : ¬ IsIsotropic φ) :
    ∃ ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ,
      ρ.PosSemidef ∧ ρ.trace = 1 ∧ IsNondegenerate (marginalA ρ) ∧
      IsNondegenerate (φ (marginalA ρ)) ∧
      pinchA (localMap φ ρ) ≠ localMap φ (pinchA ρ) := by
  have hq : ¬ ∃ c : ℝ, (blochOperator φ)ᵀ * blochOperator φ = c • 1 :=
    fun h => hi (scalar_gram_isotropic φ hφ h)
  obtain ⟨n, x, hn, hx, hnx, hcross⟩ := orthogonal_probe (blochOperator φ) hq
  have hn0 : n ≠ 0 := by
    intro h
    simp only [h, zero_dotProduct] at hn
    norm_num at hn
  have htn : blochOperator φ *ᵥ n ≠ 0 := by
    intro h
    exact hcross (by rw [h, zero_dotProduct])
  have hn2 : (1 / 2 : ℝ) • n ≠ 0 := smul_ne_zero (by norm_num) hn0
  have htn2 : (1 / 2 : ℝ) • (blochOperator φ *ᵥ n) ≠ 0 :=
    smul_ne_zero (by norm_num) htn
  refine ⟨witness n x, (witness_density n x hn hx hnx).1,
    (witness_density n x hn hx hnx).2, ?_, ?_, ?_⟩
  · rw [witness_marginal]
    exact bloch_nondegenerate _ hn2
  · rw [(mapped_marginal φ hφ n x).2]
    exact bloch_nondegenerate _ htn2
  · intro heq
    have hz := commutator_identity φ hφ n x hn hnx htn
    rw [heq, sub_self] at hz
    exact commutator_nonzero _ _ hcross hz.symm

end D5.S3.Quantum.Information.MixedUnitaryPinchingCommutation
