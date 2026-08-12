/- GID: D5/S3/QuantumStates/GNSStateCone
   generality: G
   mirror-B: D5/B/S3/QuantumStates/GNSStateCone
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Extract positivity and normalization of matrix-state expectations from the GNS norm square. -/

import D5.S3.Quantum.GNSMatrix

namespace D5.S3.QuantumStates.GNSStateCone

open scoped ComplexOrder MatrixOrder Matrix.Norms.Frobenius
open Matrix
open D5.S3.Quantum.GNSMatrix

/-- For a finite-dimensional positive trace-one matrix, the GNS norm-square identity gives
nonnegative expectations, and its identity section gives both forms of normalization. -/
theorem state_cone_sections {d : Type*} [Fintype d] [DecidableEq d]
    (rho : Matrix d d ℂ) (hRho : rho.PosSemidef)
    (hTrace : Matrix.trace rho = 1) :
    (∀ x : Matrix d d ℂ,
      Matrix.trace (rho * xᴴ * x) = (‖x * CFC.sqrt rho‖ : ℂ) ^ 2 ∧
        0 ≤ Matrix.trace (rho * xᴴ * x)) ∧
      Matrix.trace (rho * (1 : Matrix d d ℂ)ᴴ * 1) = 1 ∧
      (‖CFC.sqrt rho‖ : ℂ) ^ 2 = Matrix.trace rho ∧
      Matrix.trace rho = 1 := by
  constructor
  · intro x
    have hGns := gns_matrix_identity rho x hRho hTrace
    refine ⟨hGns, ?_⟩
    rw [hGns]
    exact Complex.sq_nonneg_iff.mpr (by simp)
  constructor
  · simpa using hTrace
  constructor
  · have hIdentity :=
      gns_matrix_identity rho (1 : Matrix d d ℂ) hRho hTrace
    simpa using hIdentity.symm
  · exact hTrace

/-- Checked evidence that the finite matrix domain is inhabited. -/
example : Matrix (Fin 1) (Fin 1) ℂ := 1

/-- The one-dimensional identity matrix witnesses simultaneous positivity and trace-one
normalization. -/
example :
    let rho : Matrix (Fin 1) (Fin 1) ℂ := 1
    rho.PosSemidef ∧ Matrix.trace rho = 1 := by
  dsimp
  constructor
  · exact Matrix.PosSemidef.one
  · simp [Matrix.trace]

#print axioms state_cone_sections

end D5.S3.QuantumStates.GNSStateCone
