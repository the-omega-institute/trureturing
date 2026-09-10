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
open scoped BigOperators ComplexOrder Matrix MatrixOrder
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
  simp [Matrix.mul_apply, copyIsometry, Fintype.sum_prod_type, Matrix.conjTranspose_apply, Matrix.one_apply, eq_comm]

private def copyMatrix (M : Matrix n n ℂ) : Matrix (n × n) (n × n) ℂ :=
  (copyIsometry (n := n)) * M * (copyIsometry (n := n))ᴴ

private theorem copyMatrix_entry (M : Matrix n n ℂ) (a b : n × n) :
    copyMatrix M a b = if a.1 = a.2 then if b.1 = b.2 then M a.1 b.1 else 0 else 0 := by
  rcases a with ⟨a₁,a₂⟩
  rcases b with ⟨c,d⟩
  by_cases hab : a₁ = a₂ <;> by_cases hcd : c = d <;>
    simp [copyMatrix, Matrix.mul_apply, copyIsometry, Matrix.conjTranspose_apply, Matrix.one_apply, hab, hcd]

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

end D5.S3.Quantum.Information.CoherentCopyCorrelationTax
