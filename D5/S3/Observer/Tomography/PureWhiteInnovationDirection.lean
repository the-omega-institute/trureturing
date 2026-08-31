/- GID: D5/S3/Observer/Tomography/PureWhiteInnovationDirection
   generality: G
   mirror-B: D5/B/S3/Observer/Tomography/PureWhiteInnovationDirection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Kernel directions of the contact analysis are nonzero floor eigenvectors. -/

import D5.S3.Observer.Tomography.ToeplitzFlatFloorMultiplicity

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Matrix
open scoped ComplexConjugate ComplexOrder

namespace D5.S3.Observer.Tomography.PureWhiteInnovationDirection

/-- The directions annihilated by the finite contact analysis are precisely the
floor directions read by the Toeplitz operator; under the strict dimension
inequality, at least one such direction is nonzero. -/
theorem pure_white_innovation_direction
    (N M : Nat)
    (omega : Real)
    (contact : Fin M -> unitary Complex)
    (weight : Fin M -> {q : Real // 0 < q})
    (contacts_lt : M < N + 1) :
    let analysis : Matrix (Fin M) (Fin (N + 1)) Complex := fun r j =>
      (Real.sqrt (weight r).1 : Complex) *
        star ((contact r : Complex) ^ j.val)
    let toeplitz :=
      (omega : Complex) •
          (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) Complex) +
        analysis.conjTranspose * analysis
    (∀ x, x ∈ analysis.mulVecLin.ker →
        x ∈ Module.End.eigenspace toeplitz.mulVecLin (omega : Complex)) ∧
      ∃ x, x ≠ 0 ∧ x ∈ analysis.mulVecLin.ker := by
  dsimp only
  let analysis : Matrix (Fin M) (Fin (N + 1)) Complex := fun r j =>
    (Real.sqrt (weight r).1 : Complex) *
      star ((contact r : Complex) ^ j.val)
  let toeplitz :=
    (omega : Complex) •
        (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) Complex) +
      analysis.conjTranspose * analysis
  change
    (∀ x, x ∈ analysis.mulVecLin.ker →
        x ∈ Module.End.eigenspace toeplitz.mulVecLin (omega : Complex)) ∧
      ∃ x, x ≠ 0 ∧ x ∈ analysis.mulVecLin.ker
  have residualPositive :
      (analysis.conjTranspose * analysis).PosSemidef :=
    Matrix.posSemidef_conjTranspose_mul_self analysis
  have rangeBound :
      Module.finrank Complex analysis.mulVecLin.range <= M := by
    calc
      Module.finrank Complex analysis.mulVecLin.range <=
          Module.finrank Complex (Fin M -> Complex) := Submodule.finrank_le _
      _ = M := by simp
  have rankNullity := analysis.mulVecLin.finrank_range_add_finrank_ker
  have domainRank :
      Module.finrank Complex (Fin (N + 1) -> Complex) = N + 1 := by
    simp
  have kernelBound :
      N + 1 - M <= Module.finrank Complex analysis.mulVecLin.ker := by
    omega
  have kernelLeEigenspace :
      analysis.mulVecLin.ker <=
        Module.End.eigenspace toeplitz.mulVecLin (omega : Complex) := by
    intro x hx
    rw [Module.End.mem_eigenspace_iff]
    change toeplitz *ᵥ x = (omega : Complex) • x
    change analysis *ᵥ x = 0 at hx
    have residualZero :
        (analysis.conjTranspose * analysis) *ᵥ x = 0 := by
      rw [← Matrix.mulVec_mulVec x analysis.conjTranspose analysis,
        hx, Matrix.mulVec_zero]
    simp [toeplitz, Matrix.add_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, residualZero]
  have kernelPositive :
      0 < Module.finrank Complex analysis.mulVecLin.ker := by
    omega
  constructor
  · exact kernelLeEigenspace
  · obtain ⟨x, x_ne_zero⟩ :=
      Module.finrank_pos_iff_exists_ne_zero.mp kernelPositive
    refine ⟨x.1, ?_, x.2⟩
    intro h
    apply x_ne_zero
    exact Subtype.ext h

#print axioms pure_white_innovation_direction

end D5.S3.Observer.Tomography.PureWhiteInnovationDirection
