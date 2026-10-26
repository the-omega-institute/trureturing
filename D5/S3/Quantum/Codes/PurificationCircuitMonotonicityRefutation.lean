/- GID: D5/S3/Quantum/Codes/PurificationCircuitMonotonicityRefutation
   generality: G
   mirror-B: D5/B/S3/Quantum/Codes/PurificationCircuitMonotonicityRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Codes/PurificationCircuitMonotonicityRefutation.claim; result=D5/S3/Quantum/Codes/PurificationCircuitMonotonicityRefutation.result; claim=D5/S3/Quantum/Codes/PurificationCircuitMonotonicityRefutation.claim
   digest: A tight noisy purification circuit reverses preparation-error monotonicity. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators

namespace D5.S3.Quantum.Codes.PurificationCircuitMonotonicityRefutation

/-- Computational-basis bitstrings on `n` qubits. -/
abbrev State (n : ℕ) := Fin n → Bool

/-- A CNOT or Toffoli gate with the required distinct qubits. -/
inductive Gate (n : ℕ) where
  | cnot (control target : Fin n) (distinct : control ≠ target)
  | toffoli (control₁ control₂ target : Fin n)
      (controlsDistinct : control₁ ≠ control₂)
      (firstDistinct : control₁ ≠ target)
      (secondDistinct : control₂ ≠ target)

/-- The qubits acted on by a gate. -/
def gateSet {n : ℕ} : Gate n → Finset (Fin n)
  | .cnot control target _ => {control, target}
  | .toffoli control₁ control₂ target _ _ _ => {control₁, control₂, target}

private def idealAction {n : ℕ} : Gate n → State n → State n
  | .cnot control target _, state =>
      Function.update state target (if state control then !state target else state target)
  | .toffoli control₁ control₂ target _ _ _, state =>
      Function.update state target
        (if state control₁ && state control₂ then !state target else state target)

private def stateWeight {n : ℕ} (state : State n) : ℕ :=
  (Finset.univ.filter (fun i => state i = true)).card

private def idealRun {n : ℕ} (circuit : List (Gate n)) (state : State n) : State n :=
  circuit.foldl (fun current gate => idealAction gate current) state

/-- The ideal circuit clears all nominated output bits on all inputs of weight at most `e`. -/
def IsPurification {n : ℕ} (circuit : List (Gate n)) (outputs : Finset (Fin n)) (e : ℕ) : Prop :=
  ∀ state, stateWeight state ≤ e → ∀ i ∈ outputs, idealRun circuit state i = false

private abbrev ProbabilityVector (n : ℕ) := State n → ℝ

private def initialDistribution {n : ℕ} (p0 : ℝ) : ProbabilityVector n := by
  classical
  exact fun state => Finset.prod Finset.univ (fun i => if state i then p0 else 1 - p0)

private def depolarize {n : ℕ} (qubits : Finset (Fin n)) (p : ℝ)
    (distribution : ProbabilityVector n) : ProbabilityVector n := by
  classical
  exact fun state =>
    (1 - p) * distribution state +
      p / (2 ^ qubits.card : ℝ) *
        Finset.sum (Finset.univ.filter (fun candidate =>
          ∀ i, i ∉ qubits → candidate i = state i)) (fun other => distribution other)

private def idleNoise {n : ℕ} : List (Fin n) → ℝ → ProbabilityVector n → ProbabilityVector n
  | [], _, distribution => distribution
  | qubit :: qubits, p, distribution =>
      idleNoise qubits p (depolarize {qubit} p distribution)

private def permute {n : ℕ} (gate : Gate n)
    (distribution : ProbabilityVector n) : ProbabilityVector n :=
  fun state => distribution (idealAction gate state)

private def noisyStep {n : ℕ} (pI pC pT : ℝ) (gate : Gate n)
    (distribution : ProbabilityVector n) : ProbabilityVector n := by
  classical
  exact
    let gateProbability := match gate with
      | .cnot _ _ _ => pC
      | .toffoli _ _ _ _ _ _ => pT
    let afterGate := depolarize (gateSet gate) gateProbability (permute gate distribution)
    idleNoise (Finset.univ \ gateSet gate).toList pI afterGate

private def noisyRun {n : ℕ} (p0 pI pC pT : ℝ) (circuit : List (Gate n)) : ProbabilityVector n :=
  circuit.foldl (fun distribution gate => noisyStep pI pC pT gate distribution)
    (initialDistribution p0)

/-- Expected fraction of nominated output bits that are true. -/
def pOut {n : ℕ} (p0 pI pC pT : ℝ) (circuit : List (Gate n))
    (outputs : Finset (Fin n)) : ℝ := by
  classical
  exact
    Finset.sum outputs (fun i =>
      Finset.sum Finset.univ (fun state =>
        if state i then noisyRun p0 pI pC pT circuit state else 0)) /
      (outputs.card : ℝ)

private def admissible (p0 pI pC pT : ℝ) : Prop :=
  0 ≤ p0 ∧ p0 < 1 / 2 ∧ 0 ≤ pI ∧ pI ≤ 1 ∧ 0 ≤ pC ∧ pC ≤ 1 ∧ 0 ≤ pT ∧ pT ≤ 1

private lemma depolarize_zero {n : ℕ} (qubits : Finset (Fin n))
    (distribution : ProbabilityVector n) : depolarize qubits 0 distribution = distribution := by
  funext state
  simp [depolarize]

private lemma idle_zero {n : ℕ} (qubits : List (Fin n))
    (distribution : ProbabilityVector n) : idleNoise qubits 0 distribution = distribution := by
  induction qubits with
  | nil => rfl
  | cons qubit qubits ih =>
      simp [idleNoise, depolarize_zero, ih]

private lemma state_eq_values (state : State 3) :
    state = ![state 0, state 1, state 2] := by
  funext j
  fin_cases j <;> rfl

private lemma state_univ_three :
    (Finset.univ : Finset (State 3)) =
      {![false, false, false], ![false, false, true], ![false, true, false],
        ![false, true, true], ![true, false, false], ![true, false, true],
        ![true, true, false], ![true, true, true]} := by
  ext state
  simp only [Finset.mem_univ, true_iff, Finset.mem_insert, Finset.mem_singleton]
  cases h0 : state 0 <;> cases h1 : state 1 <;> cases h2 : state 2
  all_goals
    have hs := state_eq_values state
    rw [hs]
    simp [h0, h1, h2]

private lemma sum_state_three (f : State 3 → ℝ) :
    Finset.sum Finset.univ f =
      f ![false, false, false] + f ![false, false, true] + f ![false, true, false] +
        f ![false, true, true] + f ![true, false, false] + f ![true, false, true] +
        f ![true, true, false] + f ![true, true, true] := by
  rw [state_univ_three]
  simp
  ring

/-- The source question's coordinatewise monotonicity assertion. -/
def claim : Prop :=
  ∀ (n k e : ℕ) (circuit : List (Gate n)) (outputs : Finset (Fin n)),
    1 ≤ k → k ≤ n → outputs.card = k → IsPurification circuit outputs e →
      Finset.sum (Finset.range (e + 1)) (fun j => n.choose j) = 2 ^ (n - k) →
      (∀ p0 pI pC pT q0 qI qC qT : ℝ,
        admissible p0 pI pC pT → admissible q0 qI qC qT →
        p0 ≤ q0 → pI = qI → pC = qC → pT = qT →
          pOut p0 pI pC pT circuit outputs ≤ pOut q0 qI qC qT circuit outputs) ∧
      (∀ p0 pI pC pT q0 qI qC qT : ℝ,
        admissible p0 pI pC pT → admissible q0 qI qC qT →
        pI ≤ qI → p0 = q0 → pC = qC → pT = qT →
          pOut p0 pI pC pT circuit outputs ≤ pOut q0 qI qC qT circuit outputs) ∧
      (∀ p0 pI pC pT q0 qI qC qT : ℝ,
        admissible p0 pI pC pT → admissible q0 qI qC qT →
        pC ≤ qC → p0 = q0 → pI = qI → pT = qT →
          pOut p0 pI pC pT circuit outputs ≤ pOut q0 qI qC qT circuit outputs) ∧
      (∀ p0 pI pC pT q0 qI qC qT : ℝ,
        admissible p0 pI pC pT → admissible q0 qI qC qT →
        pT ≤ qT → p0 = q0 → pI = qI → pC = qC →
          pOut p0 pI pC pT circuit outputs ≤ pOut q0 qI qC qT circuit outputs)

private lemma weight_ge_two {n : ℕ} (state : State n) (i j : Fin n)
    (hij : i ≠ j) (hi : state i = true) (hj : state j = true) :
    2 ≤ stateWeight state := by
  classical
  have hsub : ({i, j} : Finset (Fin n)) ⊆
      Finset.univ.filter (fun x => state x = true) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · simp [hi]
    · simp [hj]
  have hcard := Finset.card_le_card hsub
  change 2 ≤ (Finset.univ.filter (fun x => state x = true)).card
  simpa [hij] using hcard

private lemma witness_purification :
    IsPurification
      ([Gate.cnot 0 1 (by decide), Gate.cnot 1 2 (by decide),
        Gate.cnot 1 0 (by decide), Gate.cnot 0 2 (by decide),
        Gate.cnot 1 0 (by decide), Gate.toffoli 1 2 0 (by decide) (by decide) (by decide)] :
          List (Gate 3)) {0} 1 := by
  intro state hweight i hi
  have hi0 : i = 0 := by simpa using hi
  subst i
  cases h0 : state 0 <;> cases h1 : state 1 <;> cases h2 : state 2
  · norm_num [idealRun, idealAction, h0, h1, h2]
  · norm_num [idealRun, idealAction, h0, h1, h2]
  · norm_num [idealRun, idealAction, h0, h1, h2]
  · have hbad := weight_ge_two state 1 2 (by decide) h1 h2
    exfalso
    exact Nat.not_lt_of_ge hbad (Nat.lt_succ_of_le hweight)
  · norm_num [idealRun, idealAction, h0, h1, h2]
  · have hbad := weight_ge_two state 0 2 (by decide) h0 h2
    exfalso
    exact Nat.not_lt_of_ge hbad (Nat.lt_succ_of_le hweight)
  · have hbad := weight_ge_two state 0 1 (by decide) h0 h1
    exfalso
    exact Nat.not_lt_of_ge hbad (Nat.lt_succ_of_le hweight)
  · have hbad := weight_ge_two state 0 1 (by decide) h0 h1
    exfalso
    exact Nat.not_lt_of_ge hbad (Nat.lt_succ_of_le hweight)

private lemma witness_space :
    Finset.sum (Finset.range (1 + 1)) (fun j => Nat.choose 3 j) = 2 ^ (3 - 1) := by
  norm_num [Finset.sum_range_succ, Nat.choose]

set_option maxHeartbeats 4000000 in
-- The finite six-round probability reduction requires the enlarged kernel budget.
private lemma witness_evaluation_zero :
    pOut 0 0 (1 / 4) 0
      ([Gate.cnot 0 1 (by decide), Gate.cnot 1 2 (by decide),
        Gate.cnot 1 0 (by decide), Gate.cnot 0 2 (by decide),
        Gate.cnot 1 0 (by decide), Gate.toffoli 1 2 0 (by decide) (by decide) (by decide)] :
          List (Gate 3)) {0} = 1481 / 4096 := by
  norm_num (config := { maxSteps := 1000000 }) [pOut, noisyRun, noisyStep, depolarize, permute,
    initialDistribution, idealAction, gateSet, idle_zero, sum_state_three, state_univ_three,
    Fin.forall_fin_succ, Fin.prod_univ_succ, Finset.sum_filter, Function.update_apply]

set_option maxHeartbeats 4000000 in
-- The finite six-round probability reduction requires the enlarged kernel budget.
private lemma witness_evaluation_small :
    pOut (1 / 100) 0 (1 / 4) 0
      ([Gate.cnot 0 1 (by decide), Gate.cnot 1 2 (by decide),
        Gate.cnot 1 0 (by decide), Gate.cnot 0 2 (by decide),
        Gate.cnot 1 0 (by decide), Gate.toffoli 1 2 0 (by decide) (by decide) (by decide)] :
          List (Gate 3)) {0} = 23121347 / 64000000 := by
  norm_num (config := { maxSteps := 1000000 }) [pOut, noisyRun, noisyStep, depolarize, permute,
    initialDistribution, idealAction, gateSet, idle_zero, sum_state_three, state_univ_three,
    Fin.forall_fin_succ, Fin.prod_univ_succ, Finset.sum_filter, Function.update_apply]

theorem result : ¬ claim := by
  intro hclaim
  have hmono :=
    (hclaim 3 1 1
      ([Gate.cnot 0 1 (by decide), Gate.cnot 1 2 (by decide),
        Gate.cnot 1 0 (by decide), Gate.cnot 0 2 (by decide),
        Gate.cnot 1 0 (by decide), Gate.toffoli 1 2 0 (by decide) (by decide) (by decide)] :
          List (Gate 3)) {0}
      (by norm_num) (by norm_num) (by norm_num) witness_purification witness_space).1
  have hzero : admissible (0 : ℝ) 0 (1 / 4) 0 := by
    norm_num [admissible]
  have hsmall : admissible (1 / 100 : ℝ) 0 (1 / 4) 0 := by
    norm_num [admissible]
  have hineq := hmono 0 0 (1 / 4) 0 (1 / 100) 0 (1 / 4) 0
    hzero hsmall (by norm_num) rfl rfl rfl
  rw [witness_evaluation_zero, witness_evaluation_small] at hineq
  norm_num at hineq

end D5.S3.Quantum.Codes.PurificationCircuitMonotonicityRefutation
