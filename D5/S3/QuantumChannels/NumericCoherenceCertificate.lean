/- GID: D5/S3/QuantumChannels/NumericCoherenceCertificate
   generality: G
   mirror-B: D5/B/S3/QuantumChannels/NumericCoherenceCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exact two-hundred phase-damping channels preserve zero coherence; a biased diagonal witness has Hadamard seven-fiftieth coherence. -/

import D5.S3.Observer.StateNotPath

namespace D5.S3.QuantumChannels.NumericCoherenceCertificate

open D5.S3.Observer.StateNotPath
open D5.S3.Quantum.FiniteDimensional
open D5.S3.Quantum.PointerBasis
open D5.S3.Quantum.QubitWitnesses
open scoped ComplexOrder

/-- A concrete non-maximally-mixed diagonal density matrix. -/
noncomputable def biasedDiagonalDensity : QubitMatrix :=
  !![(16 : ℂ) / 25, 0; 0, (9 : ℂ) / 25]

/-- The result of applying a finite channel family from left to right. -/
def applyChannelFamily (c : Fin 200 → DampingCoefficient) (rho : QubitMatrix) : QubitMatrix :=
  (List.ofFn c).foldl (fun sigma gamma => phaseDamping gamma sigma) rho

/-- A concrete nonidentity retention coefficient for the channel-family witness. -/
noncomputable def halfDampingCoefficient : DampingCoefficient :=
  ⟨(1 : ℝ) / 2, by constructor <;> norm_num⟩

private theorem phase_damping_preserves_zero_off_diag
    (gamma : DampingCoefficient) (rho : QubitMatrix)
    (h : offDiag rho = 0) :
    offDiag (phaseDamping gamma rho) = 0 := by
  have h01 : rho 0 1 = 0 := by
    simpa [offDiag] using congrArg Prod.fst h
  have h10 : rho 1 0 = 0 := by
    simpa [offDiag] using congrArg Prod.snd h
  simp [offDiag, phaseDamping, h01, h10]

private theorem foldl_preserves_zero_off_diag
    (channels : List DampingCoefficient) (rho : QubitMatrix)
    (h : offDiag rho = 0) :
    offDiag (channels.foldl (fun sigma gamma => phaseDamping gamma sigma) rho) = 0 := by
  induction channels generalizing rho with
  | nil => simpa
  | cons gamma channels ih =>
      simpa using ih (rho := phaseDamping gamma rho)
        (phase_damping_preserves_zero_off_diag gamma rho h)

theorem biased_diagonal_density_is_state :
    biasedDiagonalDensity.PosSemidef ∧ Matrix.trace biasedDiagonalDensity = 1 := by
  constructor
  · have hDiagonal :
        (!![(16 : ℂ) / 25, 0; 0, (9 : ℂ) / 25]) =
          Matrix.diagonal (fun i : Fin 2 => if i = 0 then (16 : ℂ) / 25 else (9 : ℂ) / 25) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    change (!![(16 : ℂ) / 25, 0; 0, (9 : ℂ) / 25]).PosSemidef
    rw [hDiagonal, Matrix.posSemidef_diagonal_iff]
    intro i
    fin_cases i <;> positivity
  · norm_num [biasedDiagonalDensity, Matrix.trace, Fin.sum_univ_two]

theorem two_hundred_channel_zero_coherence
    (c : Fin 200 → DampingCoefficient) :
    offDiag biasedDiagonalDensity = 0 ∧
      offDiag (applyChannelFamily c biasedDiagonalDensity) = 0 := by
  constructor
  · simp [offDiag, biasedDiagonalDensity]
  · exact foldl_preserves_zero_off_diag (List.ofFn c) biasedDiagonalDensity
      (by simp [offDiag, biasedDiagonalDensity])

theorem two_hundred_nonidentity_family_witness :
    ∃ c : Fin 200 → DampingCoefficient,
      (∀ i, c i = halfDampingCoefficient) ∧
      (∃ i, (c i : ℝ) ≠ 1) ∧
      offDiag (applyChannelFamily c biasedDiagonalDensity) = 0 := by
  refine ⟨fun _ => halfDampingCoefficient, ?_, ?_, ?_⟩
  · intro i
    rfl
  · refine ⟨0, ?_⟩
    norm_num [halfDampingCoefficient]
  · exact (two_hundred_channel_zero_coherence (fun _ => halfDampingCoefficient)).2

theorem biased_diagonal_hadamard_certificate :
    offDiag (hadamardCoordinates biasedDiagonalDensity) =
        ((7 : ℂ) / 50, (7 : ℂ) / 50) ∧
      offDiag (hadamardCoordinates biasedDiagonalDensity) ≠ 0 := by
  have hExact :
      offDiag (hadamardCoordinates biasedDiagonalDensity) =
        ((7 : ℂ) / 50, (7 : ℂ) / 50) := by
    simp [offDiag, hadamardCoordinates, biasedDiagonalDensity]
    norm_num
  refine ⟨hExact, ?_⟩
  rw [hExact]
  norm_num

theorem two_hundred_classical_channels_and_hadamard_certificate
    (c : Fin 200 → DampingCoefficient) :
    let rho := biasedDiagonalDensity
    offDiag rho = 0 ∧
      offDiag (applyChannelFamily c rho) = 0 ∧
      rho.PosSemidef ∧ Matrix.trace rho = 1 ∧
      offDiag (hadamardCoordinates rho) =
        (((7 : ℂ) / 50), ((7 : ℂ) / 50)) := by
  dsimp
  rcases two_hundred_channel_zero_coherence c with ⟨hRho, hChannels⟩
  rcases biased_diagonal_density_is_state with ⟨hPos, hTrace⟩
  exact ⟨hRho, hChannels, hPos, hTrace, biased_diagonal_hadamard_certificate.1⟩

end D5.S3.QuantumChannels.NumericCoherenceCertificate
