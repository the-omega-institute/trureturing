/- GID: D5/S3/Quantum/Thermal/GibbsFreeEnergyStability
   generality: G
   mirror-B: D5/B/S3/Quantum/Thermal/GibbsFreeEnergyStability
   mirror-E: none(waiver:general-matrix-inequality)
   anchors: []
   digest: Derive genuine noncommuting Gibbs pressure and free-energy stability from spectral Klein and the constructed Gibbs state. -/

import D5.S3.Quantum.Divergence.SpectralKlein
import D5.S3.Quantum.Divergence.GibbsVariationalIdentity
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Tactic

/-!
Reuses the repository's normalized matrix exponential and Gibbs identity.
Klein nonnegativity is proved in SpectralKlein, not assumed here. The matrix
norm is the Euclidean operator norm, transported through the actual C-star
matrix equivalence. No commutation or operator monotonicity of exp is used.
The sign convention for the imported pressure is log Tr exp(H); thermal
free energy uses H -> -beta H with beta strictly positive.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Quantum.Thermal.GibbsFreeEnergyStability

open scoped CStarAlgebra ComplexOrder MatrixOrder Matrix.Norms.L2Operator BigOperators
open D5.S3.Quantum.Divergence.SpectralKlein
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
open D5.S3.Quantum.Divergence.GibbsVariationalIdentity

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- The actual C-star/raw matrix identification preserves the finite spectral log,
including zero eigenvalues of the first density matrix. -/
theorem raw_log (A : CStarMatrix n n ℂ) (hA : IsSelfAdjoint A) :
    CStarMatrix.ofMatrix.symm (CFC.log A) =
      CFC.log (CStarMatrix.ofMatrix.symm A) := by
  let φ := CStarMatrix.ofMatrixStarAlgEquiv (n := n) (A := ℂ)
  have hraw : IsSelfAdjoint (CStarMatrix.ofMatrix.symm A) := hA.map φ.symm
  have hcont : ContinuousOn Real.log
      (spectrum ℝ (CStarMatrix.ofMatrix.symm A)) :=
    Matrix.finite_real_spectrum.continuousOn
  have h := φ.toStarAlgHom.map_cfc Real.log (CStarMatrix.ofMatrix.symm A)
    hcont (StarAlgEquiv.isometry φ).continuous hraw (by simpa using hA)
  apply φ.injective
  simpa only [CFC.log, StarAlgEquiv.apply_symm_apply] using h.symm

/-- Faithful-reference nonnegativity for the existing repository density-state
carrier and its existing relative-entropy definition. -/
theorem gibbs_relative_entropy_nonneg (H : CStarMatrix n n ℂ)
    (hH : IsSelfAdjoint H) (ρ : DensityState n) :
    0 ≤ quantumRelativeEntropy ρ (gibbsState H hH) := by
  have hρ : (CStarMatrix.ofMatrix.symm ρ.1).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp
      (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm ρ.2.1)
  have hσ := gibbs_state_posDef H hH
  have h := faithful_relative_entropy_nonneg
    (CStarMatrix.ofMatrix.symm ρ.1)
    (CStarMatrix.ofMatrix.symm (gibbsState H hH).1)
    hρ hσ ρ.2.2 (gibbsState H hH).2.2
  have hlogρ := raw_log ρ.1 ρ.2.1.isSelfAdjoint
  have hlogσ := raw_log (gibbsState H hH).1 (gibbsState H hH).2.1.isSelfAdjoint
  simpa only [quantumRelativeEntropy, ← hlogρ, ← hlogσ] using h

/-- Expectation in an actual normalized density matrix. -/
def expectation (ρ : DensityState n) (H : CStarMatrix n n ℂ) : ℝ :=
  (Matrix.trace (CStarMatrix.ofMatrix.symm (H * ρ.1))).re

private theorem raw_expectation_le (R X : Matrix n n ℂ)
    (hR : R.PosSemidef) (hX : X.IsHermitian) (htr : Matrix.trace R = 1) :
    (Matrix.trace (R * X)).re ≤ ‖X‖ := by
  let U := hR.isHermitian.eigenvectorUnitary
  let V := hX.eigenvectorUnitary
  let a := hR.isHermitian.eigenvalues
  let x := hX.eigenvalues
  have ha : ∀ i, 0 ≤ a i := hR.eigenvalues_nonneg
  have hx (j : n) : x j ≤ ‖X‖ := by
    have h := spectrum.norm_le_norm_of_mem (hX.eigenvalues_mem_spectrum_real j)
    exact (le_abs_self (x j)).trans (by simpa only [Real.norm_eq_abs] using h)
  have hsum : ∑ i, a i = 1 := by
    have ht := trace_spectral U a
    rw [← matrix_eq_spectral hR.isHermitian, htr] at ht
    simpa using ht.symm
  rw [matrix_eq_spectral hR.isHermitian, matrix_eq_spectral hX, trace_spectral_mul]
  change (∑ i, ∑ j, a i * x j * overlap (star U * V) i j) ≤ ‖X‖
  calc
    _ ≤ ∑ i, ∑ j, a i * ‖X‖ * overlap (star U * V) i j := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hx j) (ha i)) (overlap_nonneg _ i j)
    _ = ‖X‖ := by
      simp_rw [← Finset.mul_sum, overlap_row_sum, mul_one]
      rw [← Finset.sum_mul, hsum, one_mul]

/-- No dimension factor is hidden in the expectation bound. -/
theorem expectation_abs_le (ρ : DensityState n) (H : CStarMatrix n n ℂ)
    (hH : IsSelfAdjoint H) : |expectation ρ H| ≤ ‖H‖ := by
  have hρ : (CStarMatrix.ofMatrix.symm ρ.1).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp
      (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm ρ.2.1)
  have hraw : (CStarMatrix.ofMatrix.symm H).IsHermitian :=
    hH.map CStarMatrix.ofMatrixStarAlgEquiv.symm
  have hupper := raw_expectation_le _ _ hρ hraw ρ.2.2
  have hlower := raw_expectation_le _ _ hρ hraw.neg ρ.2.2
  have hn : ‖CStarMatrix.ofMatrix.symm H‖ = ‖H‖ :=
    StarAlgEquiv.norm_map CStarMatrix.ofMatrixStarAlgEquiv.symm H
  have htrace : expectation ρ H =
      (Matrix.trace (CStarMatrix.ofMatrix.symm ρ.1 * CStarMatrix.ofMatrix.symm H)).re := by
    unfold expectation
    exact congrArg Complex.re (Matrix.trace_mul_comm _ _)
  rw [htrace, abs_le]
  constructor
  · have h := hlower
    simp only [Matrix.mul_neg, Matrix.trace_neg, Complex.neg_re, norm_neg, hn] at h
    linarith
  · simpa only [hn] using hupper

@[simp] theorem expectation_sub (ρ : DensityState n) (H K : CStarMatrix n n ℂ) :
    expectation ρ (H - K) = expectation ρ H - expectation ρ K := by
  simp [expectation, sub_mul, Matrix.trace_sub]

@[simp] theorem expectation_smul (ρ : DensityState n) (r : ℝ)
    (H : CStarMatrix n n ℂ) : expectation ρ (r • H) = r * expectation ρ H := by
  simp [expectation, smul_mul_assoc, Matrix.trace_smul, Complex.smul_re, smul_eq_mul]

/-- Gibbs variational inequality with its mathematical nonnegativity premise discharged. -/
theorem gibbs_objective_le_pressure (H : CStarMatrix n n ℂ)
    (hH : IsSelfAdjoint H) (ρ : DensityState n) :
    expectation ρ H + vonNeumannEntropy ρ ≤ Real.log (partitionFunction H) := by
  have hid := gibbs_variational_identity H hH ρ
  have hpos := gibbs_relative_entropy_nonneg H hH ρ
  change Real.log (partitionFunction H) = expectation ρ H +
    vonNeumannEntropy ρ + quantumRelativeEntropy ρ (gibbsState H hH) at hid
  linarith

/-- The explicitly constructed Gibbs density attains that objective. -/
theorem gibbs_objective_attained (H : CStarMatrix n n ℂ) (hH : IsSelfAdjoint H) :
    expectation (gibbsState H hH) H + vonNeumannEntropy (gibbsState H hH) =
      Real.log (partitionFunction H) := by
  have h := gibbs_variational_identity H hH (gibbsState H hH)
  have hz : quantumRelativeEntropy (gibbsState H hH) (gibbsState H hH) = 0 := by
    simp [quantumRelativeEntropy]
  rw [hz, add_zero] at h
  exact h.symm

/-- Dimension-free log-partition stability for arbitrary noncommuting Hermitian matrices. -/
theorem pressure_lipschitz (H K : CStarMatrix n n ℂ)
    (hH : IsSelfAdjoint H) (hK : IsSelfAdjoint K) :
    |Real.log (partitionFunction H) - Real.log (partitionFunction K)| ≤ ‖H - K‖ := by
  have hHK := gibbs_objective_le_pressure K hK (gibbsState H hH)
  have hKH := gibbs_objective_le_pressure H hH (gibbsState K hK)
  have heH := gibbs_objective_attained H hH
  have heK := gibbs_objective_attained K hK
  have hbH := expectation_abs_le (gibbsState H hH) (H - K) (hH.sub hK)
  have hbK := expectation_abs_le (gibbsState K hK) (H - K) (hH.sub hK)
  rw [expectation_sub, abs_le] at hbH hbK
  rw [abs_le]
  constructor <;> linarith

/-- Physical free energy, with the inverse-temperature sign explicit. -/
def freeEnergy (β : ℝ) (H : CStarMatrix n n ℂ) : ℝ :=
  -(β⁻¹) * Real.log (partitionFunction ((-β) • H))

/-- The constructed Gibbs divergence at inverse temperature β. -/
def excessFreeEnergy (β : ℝ) (H : CStarMatrix n n ℂ)
    (hH : IsSelfAdjoint H) (ρ : DensityState n) : ℝ :=
  β⁻¹ * quantumRelativeEntropy ρ (gibbsState ((-β) • H) (hH.smul (-β)))

/-- Lipschitz equilibrium free energy at every positive inverse temperature. -/
theorem freeEnergy_lipschitz (β : ℝ) (hβ : 0 < β)
    (H K : CStarMatrix n n ℂ) (hH : IsSelfAdjoint H) (hK : IsSelfAdjoint K) :
    |freeEnergy β H - freeEnergy β K| ≤ ‖H - K‖ := by
  have hp := pressure_lipschitz ((-β) • H) ((-β) • K) (hH.smul _) (hK.smul _)
  have hn : ‖(-β) • H - (-β) • K‖ = β * ‖H - K‖ := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hβ]
  rw [hn] at hp
  have he : |freeEnergy β H - freeEnergy β K| =
      β⁻¹ * |Real.log (partitionFunction ((-β) • H)) -
        Real.log (partitionFunction ((-β) • K))| := by
    unfold freeEnergy
    rw [← mul_sub, abs_mul, abs_neg, abs_of_pos (inv_pos.mpr hβ)]
  rw [he]
  calc
    _ ≤ β⁻¹ * (β * ‖H - K‖) := mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr hβ.le)
    _ = ‖H - K‖ := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hβ), one_mul]

/-- Physical energy-entropy-free-energy identity with a faithful Gibbs reference. -/
theorem excessFreeEnergy_identity (β : ℝ) (hβ : 0 < β)
    (H : CStarMatrix n n ℂ) (hH : IsSelfAdjoint H) (ρ : DensityState n) :
    excessFreeEnergy β H hH ρ = expectation ρ H - β⁻¹ * vonNeumannEntropy ρ - freeEnergy β H := by
  have h := gibbs_variational_identity ((-β) • H) (hH.smul _) ρ
  change Real.log (partitionFunction ((-β) • H)) =
    expectation ρ ((-β) • H) + vonNeumannEntropy ρ +
      quantumRelativeEntropy ρ (gibbsState ((-β) • H) (hH.smul _)) at h
  rw [expectation_smul] at h
  unfold excessFreeEnergy freeEnergy
  have hd : quantumRelativeEntropy ρ (gibbsState ((-β) • H) (hH.smul _)) =
      Real.log (partitionFunction ((-β) • H)) + β * expectation ρ H -
        vonNeumannEntropy ρ := by linarith
  rw [hd]
  field_simp [ne_of_gt hβ]
  <;> ring

/-- Uniform stability of the nonequilibrium free-energy excess. -/
theorem excessFreeEnergy_stability (β : ℝ) (hβ : 0 < β)
    (H K : CStarMatrix n n ℂ) (hH : IsSelfAdjoint H) (hK : IsSelfAdjoint K)
    (ρ : DensityState n) :
    |excessFreeEnergy β H hH ρ - excessFreeEnergy β K hK ρ| ≤ 2 * ‖H - K‖ := by
  rw [excessFreeEnergy_identity β hβ H hH ρ, excessFreeEnergy_identity β hβ K hK ρ]
  have he : expectation ρ H - β⁻¹ * vonNeumannEntropy ρ - freeEnergy β H -
      (expectation ρ K - β⁻¹ * vonNeumannEntropy ρ - freeEnergy β K) =
      expectation ρ (H - K) - (freeEnergy β H - freeEnergy β K) := by
    rw [expectation_sub]
    ring
  rw [he]
  calc
    _ ≤ |expectation ρ (H - K)| + |freeEnergy β H - freeEnergy β K| := abs_sub _ _
    _ ≤ ‖H - K‖ + ‖H - K‖ := add_le_add
      (expectation_abs_le ρ _ (hH.sub hK)) (freeEnergy_lipschitz β hβ H K hH hK)
    _ = _ := by ring

#print axioms gibbs_relative_entropy_nonneg
#print axioms expectation_abs_le
#print axioms pressure_lipschitz
#print axioms freeEnergy_lipschitz
#print axioms excessFreeEnergy_stability
end D5.S3.Quantum.Thermal.GibbsFreeEnergyStability
