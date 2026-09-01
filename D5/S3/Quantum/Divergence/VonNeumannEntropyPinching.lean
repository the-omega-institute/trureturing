/- GID: D5/S3/Quantum/Divergence/VonNeumannEntropyPinching
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/VonNeumannEntropyPinching
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Von Neumann entropy is compatible with the existing quantum relative entropy and satisfies the basis-pinching identity when the pinched state's matrix logarithm lies in the measured diagonal subspace; entropy monotonicity, exclusivity collapse, data processing, Maassen--Uffink Renyi bounds, and sharp Pythagoras are not covered. -/

import D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
import D5.S3.Quantum.Measurement.BasisMeasurementProjection

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'von_neumann_entropy_pinching' D5 Golden/Frozen/accepted`
     returned no matches.
   * Public hits for `vonNeumann|CFC.log|DensityState` found `DensityState` and
     `quantumRelativeEntropy` in `QuantumRelativeEntropyDefectComposition`, and the
     unrelated trace inequality `RHLinalg.vonNeumann_trace_ineq`; no public or private
     definition of von Neumann entropy was found.
   * Public `BasisMeasurementProjection.basisMeasurement` and
     `basis_measurement_is_orthogonal_projection` provide the required pinching operator
     and its diagonal orthogonality. Private hits in that module prove supporting matrix
     identities only, so they do not count as coverage and are not imported by name.
   * Pinned Mathlib supplies `CFC.log`, matrix trace linearity, and real inner-product
     infrastructure, but the searches found no packaged von Neumann pinching identity.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Divergence.VonNeumannEntropyPinching

open scoped ComplexOrder CStarAlgebra InnerProductSpace Matrix MatrixOrder

open D5.S3.Observer.Conditioning
open D5.S3.Observer.Conditioning.UnreadStateOrthogonalProjection
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Measurement.BasisMeasurementProjection
open D5.S3.Quantum.Tomography.RankOneContextCommutator

noncomputable section

/-- The von Neumann entropy `-Tr(rho log rho)` of a finite-dimensional density state. -/
noncomputable def vonNeumannEntropy
    {n : Type*} [Fintype n] [DecidableEq n] (rho : DensityState n) : ℝ :=
  -(Matrix.trace (rho.1 * CFC.log rho.1)).re

/-- The existing quantum relative entropy decomposes as negative von Neumann entropy
minus the cross-entropy trace term. -/
theorem quantum_relative_entropy_eq_neg_entropy_sub_cross
    {n : Type*} [Fintype n] [DecidableEq n] (rho sigma : DensityState n) :
    quantumRelativeEntropy rho sigma = -vonNeumannEntropy rho -
      (Matrix.trace (rho.1 * CFC.log sigma.1)).re := by
  simp only [quantumRelativeEntropy, vonNeumannEntropy, mul_sub]
  change
    (Matrix.trace
        ((CStarMatrix.ofMatrix.symm rho.1) *
            (CStarMatrix.ofMatrix.symm (CFC.log rho.1)) -
          (CStarMatrix.ofMatrix.symm rho.1) *
            (CStarMatrix.ofMatrix.symm (CFC.log sigma.1)))).re =
      - -(Matrix.trace
          ((CStarMatrix.ofMatrix.symm rho.1) *
            (CStarMatrix.ofMatrix.symm (CFC.log rho.1)))).re -
        (Matrix.trace
          ((CStarMatrix.ofMatrix.symm rho.1) *
            (CStarMatrix.ofMatrix.symm (CFC.log sigma.1)))).re
  rw [Matrix.trace_sub]
  simp only [Complex.sub_re, neg_neg]

/-- If `sigma` is the existing basis measurement of `rho` and `log sigma` remains in the
measured diagonal subspace, then pinching increases entropy by exactly the relative entropy
from `rho` to `sigma`. -/
theorem von_neumann_entropy_pinching
    {d : Nat} [NeZero d] (B : RankOneContext d)
    (hB : IsRecordMeasurement B.projector) (rho sigma : DensityState (Fin d))
    (hPinch :
      (basisMeasurement B
        ⟨rho.1, by
          change IsSelfAdjoint rho.1
          simpa only [sub_zero] using rho.2.1.1⟩).1 = sigma.1)
    (hLogDiagonal : ∃ L : HermitianSpace d,
      L.1 = CFC.log sigma.1 ∧ L ∈ diagonalSubspace B) :
    vonNeumannEntropy sigma =
      vonNeumannEntropy rho + quantumRelativeEntropy rho sigma := by
  rcases hLogDiagonal with ⟨L, hLLog, hLDiagonal⟩
  have hLRange : L ∈ LinearMap.range (basisMeasurement B) := by
    rw [basis_measurement_range B hB]
    exact hLDiagonal
  rcases hLRange with ⟨K, hK⟩
  have hLFixed : basisMeasurement B L = L := by
    rw [← hK]
    apply Subtype.ext
    change unreadState B.projector (unreadState B.projector K.1) =
      unreadState B.projector K.1
    exact unreadState_idempotent hB K.1
  let rhoHermitian : HermitianSpace d :=
    ⟨rho.1, by
      change IsSelfAdjoint rho.1
      simpa only [sub_zero] using rho.2.1.1⟩
  let sigmaHermitian : HermitianSpace d :=
    ⟨sigma.1, by
      change IsSelfAdjoint sigma.1
      simpa only [sub_zero] using sigma.2.1.1⟩
  have hUnreadRho : unreadState B.projector rho.1 = sigma.1 := by
    rw [← basisMeasurement_val B rhoHermitian]
    exact hPinch
  have hUnreadL : unreadState B.projector L.1 = L.1 := by
    rw [← basisMeasurement_val B L]
    exact congrArg Subtype.val hLFixed
  have hRhoStar : (rho.1 : Matrix (Fin d) (Fin d) ℂ)ᴴ = rho.1 := by
    have hSelfAdjoint := rhoHermitian.2
    change star rhoHermitian.1 = rhoHermitian.1 at hSelfAdjoint
    change star rho.1 = rho.1 at hSelfAdjoint
    apply Matrix.ext
    intro i j
    have hentry := congrArg
      (fun z : CStarMatrix (Fin d) (Fin d) ℂ => z i j) hSelfAdjoint
    change star (rho.1 j i) = rho.1 i j
    exact hentry
  have hSigmaStar : (sigma.1 : Matrix (Fin d) (Fin d) ℂ)ᴴ = sigma.1 := by
    have hSelfAdjoint := sigmaHermitian.2
    change star sigmaHermitian.1 = sigmaHermitian.1 at hSelfAdjoint
    change star sigma.1 = sigma.1 at hSelfAdjoint
    apply Matrix.ext
    intro i j
    have hentry := congrArg
      (fun z : CStarMatrix (Fin d) (Fin d) ℂ => z i j) hSelfAdjoint
    change star (sigma.1 j i) = sigma.1 i j
    exact hentry
  have hTrace :
      Matrix.trace (CStarMatrix.ofMatrix.symm rho.1 * L.1) =
        Matrix.trace (CStarMatrix.ofMatrix.symm sigma.1 * L.1) := by
    have hSelfAdjointness :=
      (unread_state_orthogonal_projection hB).2.1 rho.1 L.1
    rw [hUnreadRho, hUnreadL, hRhoStar, hSigmaStar] at hSelfAdjointness
    change
      Matrix.trace (CStarMatrix.ofMatrix.symm sigma.1 * L.1) =
        Matrix.trace (CStarMatrix.ofMatrix.symm rho.1 * L.1) at hSelfAdjointness
    exact hSelfAdjointness.symm
  have hCross :
      (Matrix.trace (rho.1 * CFC.log sigma.1)).re =
        (Matrix.trace (sigma.1 * CFC.log sigma.1)).re := by
    change
      (Matrix.trace (CStarMatrix.ofMatrix.symm rho.1 *
        CStarMatrix.ofMatrix.symm (CFC.log sigma.1))).re =
      (Matrix.trace (CStarMatrix.ofMatrix.symm sigma.1 *
        CStarMatrix.ofMatrix.symm (CFC.log sigma.1))).re
    change L.1 = CStarMatrix.ofMatrix.symm (CFC.log sigma.1) at hLLog
    rw [← hLLog]
    exact congrArg Complex.re hTrace
  rw [quantum_relative_entropy_eq_neg_entropy_sub_cross]
  unfold vonNeumannEntropy
  rw [hCross]
  ring

/-- The unique one-dimensional density matrix, used for a concrete compatibility smoke test. -/
noncomputable def oneDimensionalState : DensityState Unit := by
  refine ⟨(1 : CStarMatrix Unit Unit ℂ), ?_, ?_⟩
  · exact zero_le_one
  · simp [Matrix.trace, Matrix.diag]

example : quantumRelativeEntropy oneDimensionalState oneDimensionalState =
    -vonNeumannEntropy oneDimensionalState -
      (Matrix.trace
        (oneDimensionalState.1 * CFC.log oneDimensionalState.1)).re :=
  quantum_relative_entropy_eq_neg_entropy_sub_cross _ _

#print axioms von_neumann_entropy_pinching

end

end D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
