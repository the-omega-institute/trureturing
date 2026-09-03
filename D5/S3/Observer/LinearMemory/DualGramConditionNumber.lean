/- GID: D5/S3/Observer/LinearMemory/DualGramConditionNumber
   generality: G
   mirror-B: D5/B/S3/Observer/LinearMemory/DualGramConditionNumber
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Dual Gram operators have one positive-spectrum condition number and paired weak modes. -/

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Pi

/- Library-search audit trail (2026-09-03):
   * The D5 exact-hit search found the component family
     `GramNonzeroSpectrumMultiplicity`, `DualGramKernels`, and
     `DualGramVisibleRanges`, but no theorem exposing both the condition-ratio
     equality and the paired state/protocol eigenvector interpretation.
   * The D5 body-shape search found the canonical indexed observation map in
     `DualGramKernels` and `DualGramVisibleRanges`; it is instantiated inline.
   * Pinned Mathlib and a live Loogle query found no exact whole-statement hit.
     The proof directly applies Mathlib's eigenvector equation, eigenvalue
     witness, and linear-map composition APIs. No definition or abbreviation
     is introduced. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.LinearMemory.DualGramConditionNumber

/-- Coordinatewise scalar readouts construct an observation map whose state
and protocol Gram operators have identical positive-spectrum condition ratios.
At every positive singular value, a nonzero state eigenvector exists exactly
when a nonzero protocol-combination eigenvector exists at the same squared
Gram eigenvalue. -/
theorem dual_gram_condition_number
    {K V ι : Type*} [RCLike K]
    [NormedAddCommGroup V] [InnerProductSpace K V]
    [FiniteDimensional K V] [Fintype ι]
    (readout : ι -> V →ₗ[K] K) :
    let observation : V →ₗ[K] PiLp 2 (fun _ : ι => K) :=
      (WithLp.linearEquiv 2 K (ι -> K)).symm.toLinearMap.comp
        (LinearMap.pi readout)
    let statePositiveSpectrum : Set ℝ :=
      {lambda | 0 < lambda ∧
        Module.End.HasEigenvalue (observation.adjoint ∘ₗ observation)
          (RCLike.ofReal lambda)}
    let protocolPositiveSpectrum : Set ℝ :=
      {lambda | 0 < lambda ∧
        Module.End.HasEigenvalue (observation ∘ₗ observation.adjoint)
          (RCLike.ofReal lambda)}
    (sSup statePositiveSpectrum / sInf statePositiveSpectrum =
      sSup protocolPositiveSpectrum / sInf protocolPositiveSpectrum) ∧
    (∀ sigma : ℝ, 0 < sigma →
      ((∃ v : V,
          Module.End.HasEigenvector (observation.adjoint ∘ₗ observation)
            (RCLike.ofReal (sigma ^ 2)) v) ↔
        ∃ a : PiLp 2 (fun _ : ι => K),
          Module.End.HasEigenvector (observation ∘ₗ observation.adjoint)
            (RCLike.ofReal (sigma ^ 2)) a)) := by
  dsimp only
  let observation : V →ₗ[K] PiLp 2 (fun _ : ι => K) :=
    (WithLp.linearEquiv 2 K (ι -> K)).symm.toLinearMap.comp
      (LinearMap.pi readout)
  have forward {lambda : K} (lambda_ne_zero : lambda ≠ 0)
      {v : V}
      (hv : Module.End.HasEigenvector
        (observation.adjoint ∘ₗ observation) lambda v) :
      Module.End.HasEigenvector (observation ∘ₗ observation.adjoint)
        lambda (observation v) := by
    constructor
    · rw [Module.End.mem_eigenspace_iff]
      change observation
        ((observation.adjoint ∘ₗ observation) v) =
          lambda • observation v
      rw [hv.apply_eq_smul, LinearMap.map_smul]
    · intro observation_v_zero
      apply hv.2
      have lambda_smul_v_zero : lambda • v = 0 := by
        rw [← hv.apply_eq_smul]
        simp [LinearMap.comp_apply, observation_v_zero]
      exact (smul_eq_zero.mp lambda_smul_v_zero).resolve_left lambda_ne_zero
  have reverse {lambda : K} (lambda_ne_zero : lambda ≠ 0)
      {a : PiLp 2 (fun _ : ι => K)}
      (ha : Module.End.HasEigenvector
        (observation ∘ₗ observation.adjoint) lambda a) :
      Module.End.HasEigenvector (observation.adjoint ∘ₗ observation)
        lambda (observation.adjoint a) := by
    constructor
    · rw [Module.End.mem_eigenspace_iff]
      change observation.adjoint
        ((observation ∘ₗ observation.adjoint) a) =
          lambda • observation.adjoint a
      rw [ha.apply_eq_smul, LinearMap.map_smul]
    · intro adjoint_a_zero
      apply ha.2
      have lambda_smul_a_zero : lambda • a = 0 := by
        rw [← ha.apply_eq_smul]
        simp [LinearMap.comp_apply, adjoint_a_zero]
      exact (smul_eq_zero.mp lambda_smul_a_zero).resolve_left lambda_ne_zero
  have eigenvector_duality (sigma : ℝ) (sigma_pos : 0 < sigma) :
      ((∃ v : V,
          Module.End.HasEigenvector (observation.adjoint ∘ₗ observation)
            (RCLike.ofReal (sigma ^ 2)) v) ↔
        ∃ a : PiLp 2 (fun _ : ι => K),
          Module.End.HasEigenvector (observation ∘ₗ observation.adjoint)
            (RCLike.ofReal (sigma ^ 2)) a) := by
    have sigma_sq_ne_zero : RCLike.ofReal (sigma ^ 2) ≠ (0 : K) := by
      exact RCLike.ofReal_ne_zero.mpr (pow_ne_zero 2 (ne_of_gt sigma_pos))
    constructor
    · rintro ⟨v, hv⟩
      exact ⟨observation v, forward sigma_sq_ne_zero hv⟩
    · rintro ⟨a, ha⟩
      exact ⟨observation.adjoint a, reverse sigma_sq_ne_zero ha⟩
  have positive_spectra_equal :
      {lambda : ℝ | 0 < lambda ∧
          Module.End.HasEigenvalue (observation.adjoint ∘ₗ observation)
            (RCLike.ofReal lambda)} =
        {lambda : ℝ | 0 < lambda ∧
          Module.End.HasEigenvalue (observation ∘ₗ observation.adjoint)
            (RCLike.ofReal lambda)} := by
    ext lambda
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨lambda_pos, hlambda⟩
      obtain ⟨v, hv⟩ := hlambda.exists_hasEigenvector
      have lambda_ne_zero : RCLike.ofReal lambda ≠ (0 : K) :=
        RCLike.ofReal_ne_zero.mpr (ne_of_gt lambda_pos)
      exact ⟨lambda_pos,
        Module.End.hasEigenvalue_of_hasEigenvector
          (forward lambda_ne_zero hv)⟩
    · rintro ⟨lambda_pos, hlambda⟩
      obtain ⟨a, ha⟩ := hlambda.exists_hasEigenvector
      have lambda_ne_zero : RCLike.ofReal lambda ≠ (0 : K) :=
        RCLike.ofReal_ne_zero.mpr (ne_of_gt lambda_pos)
      exact ⟨lambda_pos,
        Module.End.hasEigenvalue_of_hasEigenvector
          (reverse lambda_ne_zero ha)⟩
  constructor
  · rw [positive_spectra_equal]
  · exact eigenvector_duality

#print axioms dual_gram_condition_number

end D5.S3.Observer.LinearMemory.DualGramConditionNumber
