/- GID: D5/S3/Quantum/Dynamics/LevelOneQAOAGenuineSuperposition
   generality: I
   mirror-B: D5/B/S3/Quantum/Dynamics/LevelOneQAOAGenuineSuperposition
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Dynamics/LevelOneQAOAGenuineSuperposition.claim; result=D5/S3/Quantum/Dynamics/LevelOneQAOAGenuineSuperposition.result; claim=D5/S3/Quantum/Dynamics/LevelOneQAOAGenuineSuperposition.claim
   digest: Level-one QAOA reaches a genuine four-state superposition on three qubits. -/

import D5.S3.Combinatorics.IsingUniquenessSets
import D5.S3.Quantum.Dynamics.EnergyEigenstateStationarity
import D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow
import D5.S3.Quantum.Entanglement.RandomizedGraphNegativityRefutation

/-! A counterexample to the intermediate-dimensional exclusion in Streif and Leib,
*Forbidden subspaces for level-1 QAOA and IQP circuits*, arXiv:2007.13563v1.

The phase layer separates the parity sectors of the first two qubits. The uniform and
parity vectors have mixer eigenvalues `3` and `-1`; their evolved coefficients cancel in
exactly the four non-target coordinates at angle `pi/8`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

noncomputable section

open Matrix
open scoped BigOperators

namespace D5.S3.Quantum.Dynamics.LevelOneQAOAGenuineSuperposition

open D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow
open D5.S3.Quantum.Dynamics.EnergyEigenstateStationarity
open D5.S3.Quantum.Entanglement.RandomizedGraphNegativityRefutation (plusState)

/-- The sum of the single-qubit Pauli-X operators in the computational basis. -/
def mixer (n : ℕ) : Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
  ∑ i : Fin n,
    Equiv.Perm.permMatrix ℂ
      (Equiv.piCongrRight (Function.update (fun _ : Fin n => Equiv.refl Bool)
        i Equiv.boolNot))

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

private def parity (x : Fin 3 → Bool) : ℂ :=
  (D5.S3.Combinatorics.IsingUniquenessSets.walsh {0, 1} x : ℂ)

private lemma mixer_action {n : ℕ} (v : (Fin n → Bool) → ℂ) (x : Fin n → Bool) :
    (mixer n *ᵥ v) x = ∑ i : Fin n, v (Function.update x i (!(x i))) := by
  unfold mixer
  rw [Matrix.sum_mulVec, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.permMatrix_mulVec]
  change v ((Equiv.piCongrRight (Function.update (fun _ : Fin n => Equiv.refl Bool)
    i Equiv.boolNot)) x) = _
  congr 1
  funext j
  by_cases h : j = i
  · subst j
    simp [Equiv.piCongrRight_apply]
  · simp [Equiv.piCongrRight_apply, h]

private lemma mixer_uniform :
    mixer 3 *ᵥ (1 : (Fin 3 → Bool) → ℂ) = (3 : ℂ) • (1 : (Fin 3 → Bool) → ℂ) := by
  ext x
  rw [mixer_action]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_ofNat, Pi.smul_apply, smul_eq_mul, Pi.one_apply, mul_one]

private lemma mixer_parity : mixer 3 *ᵥ parity = (-1 : ℂ) • parity := by
  ext x
  rw [mixer_action]
  simp only [parity, D5.S3.Combinatorics.IsingUniquenessSets.walsh,
    Finset.prod_pair (by decide : (0 : Fin 3) ≠ 1),
    Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one,
    Fin.isValue, Fin.succ_one_eq_two, Pi.smul_apply, smul_eq_mul,
    Function.update_self, Function.update_of_ne (by decide : (0 : Fin 3) ≠ 1),
    Function.update_of_ne (by decide : (1 : Fin 3) ≠ 0),
    Function.update_of_ne (by decide : (0 : Fin 3) ≠ 2),
    Function.update_of_ne (by decide : (1 : Fin 3) ≠ 2),
    D5.S3.Combinatorics.IsingUniquenessSets.sgn_not,
    Complex.ofReal_mul, Complex.ofReal_neg]
  ring

private lemma mixer_evolution (β : ℝ) :
    hamiltonianPropagator (mixer 3) β *ᵥ (1 : (Fin 3 → Bool) → ℂ) =
      Complex.exp (-3 * (β : ℂ) * Complex.I) • (1 : (Fin 3 → Bool) → ℂ) ∧
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

private lemma plus_three (x : Fin 3 → Bool) :
    plusState 3 x = (Real.sqrt 8 : ℂ)⁻¹ := by
  have hs : Real.sqrt 8 = Real.sqrt 2 ^ 3 := by
    have h := congrArg (fun x : NNReal => (x : ℝ)) (map_pow NNReal.sqrtHom (2 : NNReal) 3)
    norm_num [NNReal.sqrtHom, Real.coe_sqrt] at h ⊢
    exact h
  unfold plusState
  rw [inv_pow, ← hs, Complex.ofReal_inv]

private lemma phase_layer :
    hamiltonianPropagator (diagonal (fun x => (spectrum x : ℂ))) 1 *ᵥ plusState 3 =
      ((Real.sqrt 8 : ℂ)⁻¹ * ((1 - Complex.I) / 2)) • (1 : (Fin 3 → Bool) → ℂ) +
      ((Real.sqrt 8 : ℂ)⁻¹ * ((1 + Complex.I) / 2)) • parity := by
  unfold hamiltonianPropagator hamiltonianGenerator
  rw [one_smul, ← Matrix.diagonal_smul, Matrix.exp_diagonal]
  ext x
  rw [Matrix.mulVec_diagonal, Pi.coe_exp, Pi.smul_apply, smul_eq_mul,
    ← Complex.exp_eq_exp_ℂ]
  rw [plus_three]
  unfold spectrum parity
  simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul]
  split_ifs with h
  · have he : -Complex.I * ((2 * Real.pi : ℝ) : ℂ) =
        -(2 * (Real.pi : ℂ) * Complex.I) := by push_cast; ring
    rw [he, Complex.exp_neg, Complex.exp_two_pi_mul_I]
    cases h0 : x 0 <;> cases h1 : x 1 <;>
      norm_num [h0, h1] at h <;>
      norm_num [D5.S3.Combinatorics.IsingUniquenessSets.walsh,
        D5.S3.Combinatorics.IsingUniquenessSets.sgn, h0, h1] <;> ring
  · have he : -Complex.I * ((Real.pi / 2 : ℝ) : ℂ) =
        -(Real.pi : ℂ) / 2 * Complex.I := by push_cast; ring
    rw [he, Complex.exp_neg_pi_div_two_mul_I]
    cases h0 : x 0 <;> cases h1 : x 1 <;>
      norm_num [h0, h1] at h <;>
      norm_num [D5.S3.Combinatorics.IsingUniquenessSets.walsh,
        D5.S3.Combinatorics.IsingUniquenessSets.sgn, h0, h1] <;> ring

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
  unfold parity
  simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul]
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    norm_num [D5.S3.Combinatorics.IsingUniquenessSets.walsh,
      D5.S3.Combinatorics.IsingUniquenessSets.sgn, h0, h1] <;>
    ring_nf <;> simp only [Complex.I_sq] <;> ring

private lemma output_coefficient_ne_zero :
    -(Real.sqrt 8 : ℂ)⁻¹ * (1 + Complex.I) *
      Complex.exp (((Real.pi / 8 : ℝ) : ℂ) * Complex.I) ≠ 0 := by
  apply mul_ne_zero
  · apply mul_ne_zero
    · exact neg_ne_zero.mpr (inv_ne_zero (by exact_mod_cast
        (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 8)))))
    · exact Complex.ne_zero_of_re_pos (by norm_num)
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
