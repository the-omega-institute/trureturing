/- GID: D5/S3/Quantum/Divergence/PinchingIncreasesEntropy
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/PinchingIncreasesEntropy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: For a basis-pinching pair, an explicit relative-entropy nonnegativity hypothesis yields entropy monotonicity by the preceding pinching identity; the hypothesis is proved here only in dimension one, so general Klein nonnegativity, Schur--Horn pinching, and the Heisenberg-side capacity monotonicity are not covered. -/

import D5.S3.Quantum.Divergence.VonNeumannEntropyPinching

/- Library-search audit trail (2026-08-24):
   * `rg -n -F 'pinching_increases_entropy' D5 Golden/Frozen/accepted`
     returned no matches.
   * `rg -n 'relativeEntropy|quantumRelativeEntropy|nonneg|Klein|SchurHorn|majoriz'
     D5/S3/` found the public relative-entropy definition and pinching identity, but no
     public or private nonnegativity theorem. The only relevant majorization hit was the
     unrelated `SpectralPairingCapacity`.
   * Searches of pinned Mathlib and online Loogle for relative-entropy nonnegativity,
     Klein's inequality, Schur--Horn, and trace-log inequalities found no packaged result.
     Mathlib's `Analysis.InnerProductSpace.Spectrum` mentions Schur--Horn only as motivation.
   * The proof below therefore uses the public `von_neumann_entropy_pinching` identity,
     ordered-ring arithmetic, and an explicit local nonnegativity hypothesis; the general
     Klein inequality is not constructed here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Divergence.PinchingIncreasesEntropy

open scoped ComplexOrder CStarAlgebra InnerProductSpace Matrix MatrixOrder

open D5.S3.Observer.Conditioning
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
open D5.S3.Quantum.Measurement.BasisMeasurementProjection
open D5.S3.Quantum.Tomography.RankOneContextCommutator

noncomputable section

/-- Entropy gained when replacing `rho` by `sigma`. -/
def entropyGain
    {n : Type*} [Fintype n] [DecidableEq n] (rho sigma : DensityState n) : ℝ :=
  vonNeumannEntropy sigma - vonNeumannEntropy rho

/-- Quantum relative entropy is nonnegative in dimension one, where trace-one density matrices
are the unique scalar density state. -/
theorem quantum_relative_entropy_nonnegative_unit (rho sigma : DensityState Unit) :
    0 ≤ quantumRelativeEntropy rho sigma := by
  have densityState_eq_one (tau : DensityState Unit) : tau = oneDimensionalState := by
    apply Subtype.ext
    ext i j
    obtain rfl : i = () := Subsingleton.elim _ _
    obtain rfl : j = () := Subsingleton.elim _ _
    change tau.1 () () = 1
    simpa [Matrix.trace, Matrix.diag] using tau.2.2
  rw [densityState_eq_one rho, densityState_eq_one sigma]
  simp [quantumRelativeEntropy, Matrix.trace, Matrix.diag]

/-- For the pinching data of the preceding module, entropy gain is exactly relative entropy. -/
theorem pinching_entropy_gain_eq_relative_entropy
    {d : Nat} [NeZero d] (B : RankOneContext d)
    (hB : IsRecordMeasurement B.projector) (rho sigma : DensityState (Fin d))
    (hPinch :
      (basisMeasurement B
        ⟨rho.1, by
          change IsSelfAdjoint rho.1
          simpa only [sub_zero] using rho.2.1.1⟩).1 = sigma.1)
    (hLogDiagonal : ∃ L : HermitianSpace d,
      L.1 = CFC.log sigma.1 ∧ L ∈ diagonalSubspace B) :
    entropyGain rho sigma = quantumRelativeEntropy rho sigma := by
  rw [entropyGain, von_neumann_entropy_pinching B hB rho sigma hPinch hLogDiagonal]
  ring

/-- Under an explicit Klein certificate, basis pinching cannot decrease von Neumann entropy.
The certificate isolates the substantive trace-log inequality not supplied by pinned Mathlib. -/
theorem pinching_increases_entropy
    {d : Nat} [NeZero d] (B : RankOneContext d)
    (hB : IsRecordMeasurement B.projector) (rho sigma : DensityState (Fin d))
    (hPinch :
      (basisMeasurement B
        ⟨rho.1, by
          change IsSelfAdjoint rho.1
          simpa only [sub_zero] using rho.2.1.1⟩).1 = sigma.1)
    (hLogDiagonal : ∃ L : HermitianSpace d,
      L.1 = CFC.log sigma.1 ∧ L ∈ diagonalSubspace B)
    (hRelativeEntropy : 0 ≤ quantumRelativeEntropy rho sigma) :
    vonNeumannEntropy rho ≤ vonNeumannEntropy sigma := by
  apply sub_nonneg.mp
  change 0 ≤ entropyGain rho sigma
  rw [pinching_entropy_gain_eq_relative_entropy B hB rho sigma hPinch hLogDiagonal]
  exact hRelativeEntropy

example : entropyGain oneDimensionalState oneDimensionalState = 0 := by
  simp [entropyGain]

example : 0 ≤ quantumRelativeEntropy oneDimensionalState oneDimensionalState :=
  quantum_relative_entropy_nonnegative_unit _ _

#print axioms pinching_increases_entropy

end

end D5.S3.Quantum.Divergence.PinchingIncreasesEntropy
