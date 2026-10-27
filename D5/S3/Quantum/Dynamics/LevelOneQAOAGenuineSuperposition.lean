/- GID: D5/S3/Quantum/Dynamics/LevelOneQAOAGenuineSuperposition
   generality: I
   mirror-B: D5/B/S3/Quantum/Dynamics/LevelOneQAOAGenuineSuperposition
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Dynamics/LevelOneQAOAGenuineSuperposition.claim; result=D5/S3/Quantum/Dynamics/LevelOneQAOAGenuineSuperposition.result; claim=D5/S3/Quantum/Dynamics/LevelOneQAOAGenuineSuperposition.claim
   digest: Level-one QAOA reaches a genuine four-state superposition on three qubits. -/

import D5.S3.Quantum.Dynamics.EnergyEigenstateStationarity
import D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped BigOperators

namespace D5.S3.Quantum.Dynamics.LevelOneQAOAGenuineSuperposition

open D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow
open D5.S3.Quantum.Dynamics.EnergyEigenstateStationarity

/-- The sum of the single-qubit Pauli-X operators in the computational basis. -/
def mixer (n : ℕ) : Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
  ∑ i : Fin n, Matrix.of fun x y => if y = Function.update x i (!(x i)) then 1 else 0

/-- The uniform product state, with amplitude `1 / sqrt (2^n)` at every bit string. -/
def plusState (n : ℕ) : (Fin n → Bool) → ℂ :=
  fun _ => (Real.sqrt (2 ^ n : ℝ) : ℂ)⁻¹

/-- One phase-separation layer followed by one transverse-field mixing layer. -/
def qaoaState (n : ℕ) (e : (Fin n → Bool) → ℝ) (β γ : ℝ) :
    (Fin n → Bool) → ℂ :=
  hamiltonianPropagator (mixer n) β *ᵥ
    (hamiltonianPropagator (diagonal (fun x => (e x : ℂ))) γ *ᵥ plusState n)

/-- A state has nonzero amplitudes exactly at the specified computational basis states. -/
def IsGenuineSuperposition {n : ℕ} (ψ : (Fin n → Bool) → ℂ)
    (t : Finset (Fin n → Bool)) : Prop :=
  ∀ x, ψ x ≠ 0 ↔ x ∈ t

/-- The asserted exclusion of genuine target subspaces of intermediate dimension. -/
def claim : Prop :=
  ∀ (n : ℕ) (e : (Fin n → Bool) → ℝ) (β γ : ℝ)
    (t : Finset (Fin n → Bool)),
    2 < t.card → t.card < 2 ^ n → ¬ IsGenuineSuperposition (qaoaState n e β γ) t

private def targets : Finset (Fin 3 → Bool) :=
  Finset.univ.filter (fun x => x 0 ≠ x 1)

private def spectrum (x : Fin 3 → Bool) : ℝ :=
  if x 0 = x 1 then 2 * Real.pi else Real.pi / 2

private def uniform : (Fin 3 → Bool) → ℂ := fun _ => 1

private def parity (x : Fin 3 → Bool) : ℂ := if x 0 = x 1 then 1 else -1

private lemma mixer_uniform : mixer 3 *ᵥ uniform = (3 : ℂ) • uniform := by
  sorry

private lemma mixer_parity : mixer 3 *ᵥ parity = (-1 : ℂ) • parity := by
  sorry

private lemma mixer_evolution (β : ℝ) :
    hamiltonianPropagator (mixer 3) β *ᵥ uniform =
      Complex.exp (-3 * (β : ℂ) * Complex.I) • uniform ∧
    hamiltonianPropagator (mixer 3) β *ᵥ parity =
      Complex.exp ((β : ℂ) * Complex.I) • parity := by
  sorry

private lemma phase_layer :
    hamiltonianPropagator (diagonal (fun x => (spectrum x : ℂ))) 1 *ᵥ plusState 3 =
      ((Real.sqrt 8 : ℂ)⁻¹ * ((1 - Complex.I) / 2)) • uniform +
      ((Real.sqrt 8 : ℂ)⁻¹ * ((1 + Complex.I) / 2)) • parity := by
  sorry

private lemma angle_phase :
    Complex.exp (-3 * ((Real.pi / 8 : ℝ) : ℂ) * Complex.I) =
      -Complex.I * Complex.exp (((Real.pi / 8 : ℝ) : ℂ) * Complex.I) := by
  sorry

private lemma output_amplitudes (x : Fin 3 → Bool) :
    qaoaState 3 spectrum (Real.pi / 8) 1 x =
      if x 0 = x 1 then 0 else
        -(Real.sqrt 8 : ℂ)⁻¹ * (1 + Complex.I) *
          Complex.exp (((Real.pi / 8 : ℝ) : ℂ) * Complex.I) := by
  sorry

private lemma output_coefficient_ne_zero :
    -(Real.sqrt 8 : ℂ)⁻¹ * (1 + Complex.I) *
      Complex.exp (((Real.pi / 8 : ℝ) : ℂ) * Complex.I) ≠ 0 := by
  sorry

private lemma target_card : targets.card = 4 := by
  sorry

private lemma genuine_output :
    IsGenuineSuperposition (qaoaState 3 spectrum (Real.pi / 8) 1) targets := by
  intro x
  rw [output_amplitudes]
  change (if x 0 = x 1 then 0 else _) ≠ 0 ↔ x ∈ targets
  rw [targets, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  split_ifs with h
  · simp only [ne_eq, not_true_eq_false, h, not_false_eq_true]
  · exact iff_of_true output_coefficient_ne_zero h

/-- At angle `pi/8`, the three-qubit circuit has support exactly `010, 011, 100, 101`. -/
theorem result : ¬ claim := by
  intro h
  exact h 3 spectrum (Real.pi / 8) 1 targets (by rw [target_card]; norm_num)
    (by rw [target_card]; norm_num) genuine_output

end D5.S3.Quantum.Dynamics.LevelOneQAOAGenuineSuperposition
