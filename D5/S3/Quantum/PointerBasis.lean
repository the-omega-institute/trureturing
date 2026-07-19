/- GID: D5/S3/Quantum/PointerBasis
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Transport phase damping and characterize its Hadamard pointer basis. -/

import D5.S3.Quantum.Decoherence

namespace D5.S3.Quantum.PointerBasis

open D5.S3.Quantum.Decoherence
open D5.S3.Quantum.FiniteDimensional
open D5.S3.Quantum.QubitWitnesses

/-- Phase damping transported through a coordinate equivalence records in that basis. -/
def phaseDampingInBasis (coordinates : QubitMatrix ≃ QubitMatrix)
    (c : DampingCoefficient) (rho : QubitMatrix) : QubitMatrix :=
  coordinates.symm (phaseDamping c (coordinates rho))

/-- A nontrivial transported damping channel fixes exactly the matrices diagonal in
the coordinates selected by its record rule. -/
theorem phase_damping_in_basis_fixed_iff (coordinates : QubitMatrix ≃ QubitMatrix)
    (c : DampingCoefficient) (hCoefficient : (c : Real) ≠ 1) (rho : QubitMatrix) :
    phaseDampingInBasis coordinates c rho = rho ↔
      ∀ i j, i ≠ j -> coordinates rho i j = 0 := by
  unfold phaseDampingInBasis
  rw [coordinates.symm_apply_eq]
  exact phase_damping_fixed_iff_diagonal c hCoefficient (coordinates rho)

/-- Conjugation by the normalized two-point Hadamard transform, written entrywise. -/
noncomputable def hadamardCoordinates (rho : QubitMatrix) : QubitMatrix :=
  !![(rho 0 0 + rho 0 1 + rho 1 0 + rho 1 1) / 2,
      (rho 0 0 - rho 0 1 + rho 1 0 - rho 1 1) / 2;
     (rho 0 0 + rho 0 1 - rho 1 0 - rho 1 1) / 2,
      (rho 0 0 - rho 0 1 - rho 1 0 + rho 1 1) / 2]

/-- The two-point Hadamard coordinate transform is an involution. -/
theorem hadamard_coordinates_involutive (rho : QubitMatrix) :
    hadamardCoordinates (hadamardCoordinates rho) = rho := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hadamardCoordinates] <;> ring

/-- Hadamard/Fourier coordinates as an explicit equivalence on qubit matrices. -/
noncomputable def hadamardCoordinateEquiv : QubitMatrix ≃ QubitMatrix where
  toFun := hadamardCoordinates
  invFun := hadamardCoordinates
  left_inv := hadamard_coordinates_involutive
  right_inv := hadamard_coordinates_involutive

/-- Phase damping after switching to the two-point Fourier coordinates. -/
noncomputable def fourierPhaseDamping (c : DampingCoefficient)
    (rho : QubitMatrix) : QubitMatrix :=
  phaseDampingInBasis hadamardCoordinateEquiv c rho

/-- Fourier-record damping fixes exactly the matrices diagonal in Fourier coordinates. -/
theorem fourier_phase_damping_fixed_iff (c : DampingCoefficient)
    (hCoefficient : (c : Real) ≠ 1) (rho : QubitMatrix) :
    fourierPhaseDamping c rho = rho ↔
      ∀ i j, i ≠ j -> hadamardCoordinates rho i j = 0 := by
  simpa [fourierPhaseDamping, hadamardCoordinateEquiv] using
    phase_damping_in_basis_fixed_iff hadamardCoordinateEquiv c hCoefficient rho

end D5.S3.Quantum.PointerBasis
