/- GID: D5/S3/Quantum/Matrix/LinGProperty/PhaseRotation
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/LinGProperty/PhaseRotation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [D5/S3/Quantum/Schatten/SingularValueOrder]
   utility: none
   digest: Phase normalization preserves positive block matrices and sorted singular values. -/

import D5.S3.Quantum.Schatten.SingularValueOrder
import Mathlib.Analysis.Complex.Basic

noncomputable section
open Matrix
open scoped ComplexOrder
namespace D5.S3.Quantum.Matrix.LinGProperty

variable {n : ℕ}

/-- Unit scalar multiplication of the off-diagonal block preserves block positivity. -/
theorem block_posSemidef_phase {A X B : Matrix (Fin n) (Fin n) ℂ}
    (hW : (fromBlocks A X Xᴴ B).PosSemidef) (z : ℂ) (hz : ‖z‖ = 1) :
    (fromBlocks A (z • X) (z • X)ᴴ B).PosSemidef := by
  let D : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
    fromBlocks (z • 1) 0 0 1
  have hzstar : z * star z = 1 := by
    rw [Complex.star_def, Complex.mul_conj', hz]
    norm_num
  have hzstar' : (starRingEnd ℂ) z * z = 1 := by
    simpa only [starRingEnd_apply, mul_comm] using hzstar
  have he : D * fromBlocks A X Xᴴ B * Dᴴ = fromBlocks A (z • X) (z • X)ᴴ B := by
    simp [D, fromBlocks_multiply, fromBlocks_conjTranspose, conjTranspose_smul,
      smul_mul_assoc, mul_smul_comm, smul_smul, hzstar']
  rw [← he]
  exact hW.mul_mul_conjTranspose_same D

/-- Unit scalar multiplication preserves every sorted singular value. -/
theorem singularValuesSorted_phase (X : Matrix (Fin n) (Fin n) ℂ)
    (z : ℂ) (hz : ‖z‖ = 1) (j : Fin (Fintype.card (Fin n))) :
    singularValuesSorted (z • X) j = singularValuesSorted X j := by
  have hzstar : z * star z = 1 := by
    rw [Complex.star_def, Complex.mul_conj', hz]
    norm_num
  have hzstar' : (starRingEnd ℂ) z * z = 1 := by
    simpa only [starRingEnd_apply, mul_comm] using hzstar
  have hU : (z • (1 : Matrix (Fin n) (Fin n) ℂ)) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    simp [star_eq_conjTranspose, conjTranspose_smul, smul_mul_smul, smul_smul, hzstar']
  simpa using Schatten.singularValuesSorted_unitary_mul (z • 1) X hU j

/-- There is a unit phase making the trace real and nonnegative. -/
theorem exists_trace_phase (X : Matrix (Fin n) (Fin n) ℂ) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ (z • X).trace = (‖X.trace‖ : ℂ) := by
  obtain ⟨z, hz, ht⟩ := Complex.exists_norm_eq_mul_self X.trace
  exact ⟨z, hz, by simpa only [trace_smul, smul_eq_mul] using ht.symm⟩

end D5.S3.Quantum.Matrix.LinGProperty
