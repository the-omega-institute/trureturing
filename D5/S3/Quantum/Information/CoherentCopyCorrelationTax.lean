/- GID: D5/S3/Quantum/Information/CoherentCopyCorrelationTax
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/CoherentCopyCorrelationTax
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Coherent premeasurement preserves entropy and splits correlation into record and tax. -/

import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators ComplexOrder CStarAlgebra Matrix MatrixOrder
open Matrix
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity
open D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow
open D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics

namespace D5.S3.Quantum.Information.CoherentCopyCorrelationTax
variable {n : Type*} [Fintype n] [DecidableEq n]

private def copyIsometry : Matrix (n × n) n ℂ :=
  fun a i => if a.1 = a.2 then (1 : Matrix n n ℂ) a.1 i else 0

private theorem copyIsometry_star_mul :
    (copyIsometry (n := n))ᴴ * (copyIsometry (n := n)) = 1 := by
  ext i j
  simp [Matrix.mul_apply, copyIsometry, Fintype.sum_prod_type,
    Matrix.conjTranspose_apply, Matrix.one_apply, eq_comm]

private def copyMatrix (M : Matrix n n ℂ) : Matrix (n × n) (n × n) ℂ :=
  (copyIsometry (n := n)) * M * (copyIsometry (n := n))ᴴ

private theorem copyMatrix_entry (M : Matrix n n ℂ) (a b : n × n) :
    copyMatrix M a b = if a.1 = a.2 then if b.1 = b.2 then M a.1 b.1 else 0 else 0 := by
  rcases a with ⟨a₁,a₂⟩
  rcases b with ⟨c,d⟩
  by_cases hab : a₁ = a₂ <;> by_cases hcd : c = d <;>
    simp [copyMatrix, Matrix.mul_apply, copyIsometry, Matrix.conjTranspose_apply,
      Matrix.one_apply, hab, hcd]

private theorem trace_copyMatrix (M : Matrix n n ℂ) : (copyMatrix M).trace = M.trace := by
  rw [copyMatrix, Matrix.trace_mul_cycle, copyIsometry_star_mul, Matrix.one_mul]

/-- The coherent premeasurement state associated with the standard rank-one basis. -/
noncomputable def coherentCopyState (rho : DensityState n) : DensityState (n × n) := by
  refine ⟨CStarMatrix.ofMatrix (copyMatrix rho.1), ?_, ?_⟩
  · apply map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
    apply Matrix.PosSemidef.nonneg
    unfold copyMatrix
    apply Matrix.PosSemidef.mul_mul_conjTranspose_same
    exact Matrix.nonneg_iff_posSemidef.mp
      (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm rho.2.1)
  · exact (trace_copyMatrix rho.1).trans rho.2.2

/-- The joint state retains every input matrix entry between the correlated basis vectors. -/
theorem coherentCopyState_correlated_entry (rho : DensityState n) (i j : n) :
    (coherentCopyState rho).1 (i,i) (j,j) = rho.1 i j := by
  exact (copyMatrix_entry rho.1 (i,i) (j,j)).trans (by simp)

private theorem partialTraceRight_copyMatrix (M : Matrix n n ℂ) :
    partialTraceRight (copyMatrix M) = Matrix.diagonal (fun i => M i i) := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [partialTraceRight, copyMatrix_entry]
  · simp [partialTraceRight, copyMatrix_entry, h, Ne.symm h]

private theorem partialTraceLeft_copyMatrix (M : Matrix n n ℂ) :
    partialTraceLeft (copyMatrix M) = Matrix.diagonal (fun i => M i i) := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [partialTraceLeft, copyMatrix_entry]
  · simp [partialTraceLeft, copyMatrix_entry, h]

/-- Tracing out the record gives the existing basis pinching of the input state. -/
theorem marginalRight_coherentCopyState (rho : DensityState n) :
    marginalRight (coherentCopyState rho) = basisPinchingState rho := by
  apply Subtype.ext
  exact congrArg CStarMatrix.ofMatrix (partialTraceRight_copyMatrix rho.1)

/-- Tracing out the system gives the diagonal record state with the same Born weights. -/
theorem marginalLeft_coherentCopyState (rho : DensityState n) :
    marginalLeft (coherentCopyState rho) = basisPinchingState rho := by
  apply Subtype.ext
  exact congrArg CStarMatrix.ofMatrix (partialTraceLeft_copyMatrix rho.1)

private theorem copyMatrix_mul (A B : Matrix n n ℂ) :
    copyMatrix (A * B) = copyMatrix A * copyMatrix B := by
  let V : Matrix (n × n) n ℂ := copyIsometry
  have hV : Vᴴ * V = 1 := copyIsometry_star_mul
  change V * (A * B) * Vᴴ = (V * A * Vᴴ) * (V * B * Vᴴ)
  calc
    _ = V * A * (Vᴴ * V) * B * Vᴴ := by
      rw [hV]
      simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

private def copyHom :
    CStarMatrix n n ℂ →⋆ₙₐ[ℂ] CStarMatrix (n × n) (n × n) ℂ where
  toFun M := CStarMatrix.ofMatrix (copyMatrix M)
  map_zero' := by
    change copyMatrix (0 : Matrix n n ℂ) = 0
    simp only [copyMatrix, Matrix.mul_zero, Matrix.zero_mul]
  map_add' A B := by
    change copyMatrix (CStarMatrix.ofMatrix.symm A + CStarMatrix.ofMatrix.symm B) =
      copyMatrix (CStarMatrix.ofMatrix.symm A) + copyMatrix (CStarMatrix.ofMatrix.symm B)
    simp only [copyMatrix, Matrix.mul_add, Matrix.add_mul]
  map_mul' A B := copyMatrix_mul (CStarMatrix.ofMatrix.symm A) (CStarMatrix.ofMatrix.symm B)
  map_smul' r A := by
    change copyMatrix (r • CStarMatrix.ofMatrix.symm A) =
      r • copyMatrix (CStarMatrix.ofMatrix.symm A)
    simp only [copyMatrix, Matrix.mul_smul, Matrix.smul_mul]
  map_star' A := by
    change copyMatrix ((CStarMatrix.ofMatrix.symm A)ᴴ) = (copyMatrix (CStarMatrix.ofMatrix.symm A))ᴴ
    simp only [copyMatrix, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    exact Matrix.mul_assoc _ _ _

private theorem copyHom_continuous : Continuous (copyHom (n := n)) := by
  let : FiniteDimensional ℂ (CStarMatrix n n ℂ) :=
    FiniteDimensional.of_injective (CStarMatrix.ofMatrixₗ (R := ℂ)).symm.toLinearMap
      (CStarMatrix.ofMatrixₗ (R := ℂ)).symm.injective
  let L : CStarMatrix n n ℂ →ₗ[ℂ] CStarMatrix (n × n) (n × n) ℂ :=
    { toFun := copyHom
      map_add' := map_add copyHom
      map_smul' := map_smul copyHom }
  exact L.continuous_of_finiteDimensional

private theorem log_continuous_quasispectrum (A : CStarMatrix n n ℂ) :
    ContinuousOn Real.log (quasispectrum ℝ A) := by
  change ContinuousOn Real.log (quasispectrum ℝ (CStarMatrix.ofMatrix.symm A))
  rw [quasispectrum_eq_spectrum_union_zero]
  exact ((CStarMatrix.ofMatrix.symm A).finite_real_spectrum.union
    (Set.finite_singleton 0)).continuousOn _

private theorem copyHom_log (rho : DensityState n) :
    copyHom (CFC.log rho.1) = CFC.log (coherentCopyState rho).1 := by
  let : ContinuousFunctionalCalculus ℝ (CStarMatrix n n ℂ) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  let : ContinuousFunctionalCalculus ℝ (CStarMatrix (n × n) (n × n) ℂ) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  have ha : IsSelfAdjoint rho.1 := by simpa only [sub_zero] using rho.2.1.1
  have hb : IsSelfAdjoint (copyHom rho.1) := ha.map copyHom
  have h := (copyHom (n := n)).map_cfcₙ (R := ℝ) Real.log rho.1
    (log_continuous_quasispectrum rho.1) Real.log_zero copyHom_continuous ha hb
  rw [cfcₙ_eq_cfc (log_continuous_quasispectrum rho.1) Real.log_zero,
    cfcₙ_eq_cfc (log_continuous_quasispectrum (copyHom rho.1)) Real.log_zero] at h
  exact h

/-- Coherent copying is an isometric dilation and preserves entropy, including singular states. -/
theorem vonNeumannEntropy_coherentCopyState (rho : DensityState n) :
    vonNeumannEntropy (coherentCopyState rho) = vonNeumannEntropy rho := by
  unfold vonNeumannEntropy
  rw [← copyHom_log]
  change -(Matrix.trace (copyHom rho.1 * copyHom (CFC.log rho.1))).re = _
  rw [← map_mul]
  exact congrArg (fun z : ℂ => -z.re) (trace_copyMatrix (rho.1 * CFC.log rho.1))

private theorem unitaryConjugateState_one (rho : DensityState n) :
    unitaryConjugateState 1 (show (1 : Matrix n n ℂ) ∈ Matrix.unitaryGroup n ℂ from
      (Matrix.unitaryGroup n ℂ).one_mem) rho = rho := by
  apply Subtype.ext
  change CStarMatrix.ofMatrix (1 * densityMatrix rho * star (1 : Matrix n n ℂ)) = _
  simp only [star_one, Matrix.one_mul, Matrix.mul_one]
  rfl

private theorem pinching_entropy_identity (rho : DensityState n) :
    vonNeumannEntropy (basisPinchingState rho) = vonNeumannEntropy rho +
      quantumRelativeEntropy rho (basisPinchingState rho) := by
  let f : ℕ → DensityState n := fun k => (basisPinchingState^[k]) rho
  have hstep (k : ℕ) :
      f (k+1) = basisPinchingState (unitaryConjugateState 1
        (Matrix.unitaryGroup n ℂ).one_mem (f k)) := by
    rw [unitaryConjugateState_one]
    exact Function.iterate_succ_apply' _ _ _
  have h := (entropy_production_coherence_deletion_identity 1
    (Matrix.unitaryGroup n ℂ).one_mem f hstep).1 0 |>.1
  simp only [f, Function.iterate_zero_apply, Function.iterate_one, zero_add,
    unitaryConjugateState_one] at h
  linarith

/-- System-record correlation equals the record entropy plus the destroyed coherence. -/
theorem coherent_copy_correlation_tax (rho : DensityState n) :
    quantumMutualInformation (coherentCopyState rho) =
      vonNeumannEntropy (basisPinchingState rho) +
        quantumRelativeEntropy rho (basisPinchingState rho) := by
  unfold quantumMutualInformation
  rw [marginalRight_coherentCopyState, marginalLeft_coherentCopyState,
    vonNeumannEntropy_coherentCopyState]
  have h := pinching_entropy_identity rho
  linarith

#print axioms coherent_copy_correlation_tax

end D5.S3.Quantum.Information.CoherentCopyCorrelationTax
