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
set_option linter.style.longLine false

/-! The phase layer separates the parity sectors of the first two qubits. The uniform and
parity vectors have mixer eigenvalues `3` and `-1`; their evolved coefficients cancel in
exactly the four non-target coordinates at angle `pi/8`. -/

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

private lemma mixer_action {n : ℕ} (v : (Fin n → Bool) → ℂ) (x : Fin n → Bool) :
    (mixer n *ᵥ v) x = ∑ i : Fin n, v (Function.update x i (!(x i))) := by
  rw [mixer, Matrix.sum_mulVec, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  change (∑ y, (if y = Function.update x i (!(x i)) then (1 : ℂ) else 0) * v y) = _
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

private lemma mixer_uniform : mixer 3 *ᵥ uniform = (3 : ℂ) • uniform := by
  ext x
  rw [mixer_action]
  simp only [uniform, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_ofNat, Pi.smul_apply, smul_eq_mul, mul_one]

private lemma mixer_parity : mixer 3 *ᵥ parity = (-1 : ℂ) • parity := by
  ext x
  rw [mixer_action]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one,
    Fin.isValue, Fin.succ_one_eq_two, parity, Pi.smul_apply, smul_eq_mul,
    Function.update_self, Function.update_of_ne (by decide : (0 : Fin 3) ≠ 1),
    Function.update_of_ne (by decide : (1 : Fin 3) ≠ 0),
    Function.update_of_ne (by decide : (0 : Fin 3) ≠ 2),
    Function.update_of_ne (by decide : (1 : Fin 3) ≠ 2)]
  cases x 0 <;> cases x 1 <;> norm_num

private lemma mixer_evolution (β : ℝ) :
    hamiltonianPropagator (mixer 3) β *ᵥ uniform =
      Complex.exp (-3 * (β : ℂ) * Complex.I) • uniform ∧
    hamiltonianPropagator (mixer 3) β *ᵥ parity =
      Complex.exp ((β : ℂ) * Complex.I) • parity := by
  constructor
  · unfold hamiltonianPropagator hamiltonianGenerator
    apply exp_mulVec_of_eigenvector
    rw [Matrix.smul_mulVec, Matrix.smul_mulVec, mixer_uniform, smul_smul]
    ext x
    simp only [Pi.smul_apply, smul_eq_mul, Complex.real_smul]
    ring
  · unfold hamiltonianPropagator hamiltonianGenerator
    apply exp_mulVec_of_eigenvector
    rw [Matrix.smul_mulVec, Matrix.smul_mulVec, mixer_parity, smul_smul]
    ext x
    simp only [Pi.smul_apply, smul_eq_mul, Complex.real_smul]
    ring

private lemma phase_layer :
    hamiltonianPropagator (diagonal (fun x => (spectrum x : ℂ))) 1 *ᵥ plusState 3 =
      ((Real.sqrt 8 : ℂ)⁻¹ * ((1 - Complex.I) / 2)) • uniform +
      ((Real.sqrt 8 : ℂ)⁻¹ * ((1 + Complex.I) / 2)) • parity := by
  unfold hamiltonianPropagator hamiltonianGenerator
  rw [one_smul, ← Matrix.diagonal_smul, Matrix.exp_diagonal]
  ext x
  rw [Matrix.mulVec_diagonal, Pi.coe_exp, Pi.smul_apply, smul_eq_mul,
    ← Complex.exp_eq_exp_ℂ]
  simp only [plusState, spectrum, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    uniform, parity]
  norm_num only [Nat.reducePow]
  split_ifs with h
  · have he : -Complex.I * ((2 * Real.pi : ℝ) : ℂ) =
        -(2 * (Real.pi : ℂ) * Complex.I) := by push_cast; ring
    rw [he, Complex.exp_neg, Complex.exp_two_pi_mul_I]
    norm_num
    ring
  · have he : -Complex.I * ((Real.pi / 2 : ℝ) : ℂ) =
        -(Real.pi : ℂ) / 2 * Complex.I := by push_cast; ring
    rw [he, Complex.exp_neg_pi_div_two_mul_I]
    ring

private lemma angle_phase :
    Complex.exp (-3 * ((Real.pi / 8 : ℝ) : ℂ) * Complex.I) =
      -Complex.I * Complex.exp (((Real.pi / 8 : ℝ) : ℂ) * Complex.I) := by
  have h : -3 * ((Real.pi / 8 : ℝ) : ℂ) * Complex.I =
      -(Real.pi : ℂ) / 2 * Complex.I +
        ((Real.pi / 8 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.exp_add, Complex.exp_neg_pi_div_two_mul_I]

private lemma output_amplitudes (x : Fin 3 → Bool) :
    qaoaState 3 spectrum (Real.pi / 8) 1 x =
      if x 0 = x 1 then 0 else
        -(Real.sqrt 8 : ℂ)⁻¹ * (1 + Complex.I) *
          Complex.exp (((Real.pi / 8 : ℝ) : ℂ) * Complex.I) := by
  unfold qaoaState
  rw [phase_layer, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
    (mixer_evolution (Real.pi / 8)).1, (mixer_evolution (Real.pi / 8)).2, angle_phase]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, uniform, parity]
  split_ifs <;> ring_nf <;> simp only [Complex.I_sq] <;> ring

private lemma output_coefficient_ne_zero :
    -(Real.sqrt 8 : ℂ)⁻¹ * (1 + Complex.I) *
      Complex.exp (((Real.pi / 8 : ℝ) : ℂ) * Complex.I) ≠ 0 := by
  apply mul_ne_zero
  · apply mul_ne_zero
    · exact neg_ne_zero.mpr (inv_ne_zero (by exact_mod_cast
        (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 8)))))
    · intro h
      have k := congrArg Complex.re h
      norm_num at k
  · exact Complex.exp_ne_zero _

private lemma target_card : targets.card = 4 := by
  decide

private lemma genuine_output :
    IsGenuineSuperposition (qaoaState 3 spectrum (Real.pi / 8) 1) targets := by
  intro x
  rw [output_amplitudes]
  rw [targets, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  split_ifs with h
  · simp only [ne_eq, not_true_eq_false, h]
  · exact iff_of_true output_coefficient_ne_zero h

/-- At angle `pi/8`, the three-qubit circuit has support exactly `010, 011, 100, 101`. -/
theorem result : ¬ claim := by
  intro h
  exact h 3 spectrum (Real.pi / 8) 1 targets (by rw [target_card]; norm_num)
    (by rw [target_card]; norm_num) genuine_output

end D5.S3.Quantum.Dynamics.LevelOneQAOAGenuineSuperposition
