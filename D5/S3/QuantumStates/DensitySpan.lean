/- GID: D5/S3/QuantumStates/DensitySpan
   generality: G
   mirror-B: D5/B/S3/QuantumStates/DensitySpan
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Density matrices form the full real Hermitian operator span in every finite dimension. -/

/- all_density_tomographically_complete: proof_shape: bind-only; escape_witness: none;
   consumer: WeightedRayStochasticRigidity.density_trace_ext and the concealment refutation. -/

import D5.S3.Quantum.Measurement.BasisMeasurementProjection
import Mathlib.Analysis.CStarAlgebra.SpecialFunctions.PosPart

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix
open D5.S3.Quantum.Measurement.BasisMeasurementProjection (HermitianSpace)

namespace D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation

/-- A positive semidefinite trace-one matrix is a density matrix. -/
def IsDensity {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  A.PosSemidef ∧ Matrix.trace A = 1

end D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation

namespace D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation

open D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation (IsDensity)

/-- A density set spans the real Hermitian operator space. -/
def TomographicallyComplete {d : ℕ} (T : Set (Matrix (Fin d) (Fin d) ℂ)) : Prop :=
  (∀ ρ ∈ T, IsDensity ρ) ∧ Submodule.span ℝ T = HermitianSpace d

/-- All density matrices span the Hermitian operator space over the reals. -/
theorem all_density_tomographically_complete (d : ℕ) :
    TomographicallyComplete {ρ : Matrix (Fin d) (Fin d) ℂ | IsDensity ρ} := by
  refine ⟨fun _ h => h, le_antisymm ?_ ?_⟩
  · apply Submodule.span_le.mpr
    intro A hA
    exact hA.1.isHermitian
  · let S := Submodule.span ℝ {ρ : Matrix (Fin d) (Fin d) ℂ | IsDensity ρ}
    have positive_mem (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.PosSemidef) : A ∈ S := by
      by_cases hz : trace A = 0
      · rw [hA.trace_eq_zero_iff.mp hz]
        exact S.zero_mem
      · let r := (trace A).re
        have hrreal : (r : ℂ) = trace A := by
          apply Complex.ext
          · rfl
          · exact (Complex.nonneg_iff.mp hA.trace_nonneg).2
        have hrne : r ≠ 0 := by
          intro hr
          apply hz
          rw [← hrreal, hr, Complex.ofReal_zero]
        have hr : 0 < r := lt_of_le_of_ne (Complex.nonneg_iff.mp hA.trace_nonneg).1
          (Ne.symm hrne)
        have hρ : IsDensity (r⁻¹ • A) := by
          refine ⟨hA.smul (inv_nonneg.mpr hr.le), ?_⟩
          rw [Matrix.trace_smul, ← hrreal, Complex.real_smul]
          simp [hrne]
        have hmem := S.smul_mem r (Submodule.subset_span hρ)
        simpa only [smul_smul, mul_inv_cancel₀ hrne, one_smul] using hmem
    intro A hA
    change IsSelfAdjoint A at hA
    rw [← CFC.posPart_sub_negPart A hA]
    exact S.sub_mem
      (positive_mem _ (Matrix.nonneg_iff_posSemidef.mp (CFC.posPart_nonneg A)))
      (positive_mem _ (Matrix.nonneg_iff_posSemidef.mp (CFC.negPart_nonneg A)))

end D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation
