/- GID: D5/S3/Observer/StateNotPath
   generality: G
   mirror-B: D5/B/S3/Observer/StateNotPath
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Separate classical diagonal iteration from one-step Hadamard coherence. -/

import D5.S3.Quantum.PointerBasis

namespace D5.S3.Observer.StateNotPath

open D5.S3.Quantum.FiniteDimensional
open D5.S3.Quantum.PointerBasis
open D5.S3.Quantum.QubitWitnesses

/-- The two off-diagonal entries of a qubit matrix. -/
def offDiag (rho : QubitMatrix) : ℂ × ℂ :=
  (rho 0 1, rho 1 0)

/-- The classical diagonal channel with coherence-retention coefficient `c`. -/
def classicalDiagonalChannel (c : DampingCoefficient) : QubitMatrix → QubitMatrix :=
  phaseDamping c

/-- The density matrix of the computational basis state `|0>`. -/
def basisZeroDensity : QubitMatrix :=
  !![1, 0; 0, 0]

/-- A classical diagonal channel cannot create off-diagonal entries from a diagonal input,
after any finite number of iterations. -/
theorem classical_diagonal_iterates_off_diag_eq_zero
    (c : DampingCoefficient) (n : ℕ) (rho : QubitMatrix)
    (hDiagonal : offDiag rho = 0) :
    offDiag (((classicalDiagonalChannel c)^[n]) rho) = 0 := by
  induction n with
  | zero => simpa using hDiagonal
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      have h01 : ((classicalDiagonalChannel c)^[n] rho) 0 1 = 0 := by
        simpa [offDiag] using congrArg Prod.fst ih
      have h10 : ((classicalDiagonalChannel c)^[n] rho) 1 0 = 0 := by
        simpa [offDiag] using congrArg Prod.snd ih
      have h01' : (phaseDamping c)^[n] rho 0 1 = 0 := by
        simpa [classicalDiagonalChannel] using h01
      have h10' : (phaseDamping c)^[n] rho 1 0 = 0 := by
        simpa [classicalDiagonalChannel] using h10
      simp [offDiag, classicalDiagonalChannel, phaseDamping, h01', h10']

/-- One Hadamard conjugation of the computational basis state creates exact nonzero coherence. -/
theorem hadamard_basis_zero_off_diag_certificate :
    offDiag (hadamardCoordinates basisZeroDensity) =
        ((1 : ℂ) / 2, (1 : ℂ) / 2) ∧
      offDiag (hadamardCoordinates basisZeroDensity) ≠ 0 := by
  have hExact :
      offDiag (hadamardCoordinates basisZeroDensity) =
        ((1 : ℂ) / 2, (1 : ℂ) / 2) := by
    simp [offDiag, hadamardCoordinates, basisZeroDensity]
  refine ⟨hExact, ?_⟩
  rw [hExact]
  norm_num

end D5.S3.Observer.StateNotPath
