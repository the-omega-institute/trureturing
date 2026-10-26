/- GID: D5/S3/Quantum/Codes/PurificationCircuitMonotonicityRefutation
   generality: G
   mirror-B: D5/B/S3/Quantum/Codes/PurificationCircuitMonotonicityRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Codes/PurificationCircuitMonotonicityRefutation.claim; result=D5/S3/Quantum/Codes/PurificationCircuitMonotonicityRefutation.result; claim=D5/S3/Quantum/Codes/PurificationCircuitMonotonicityRefutation.claim
   digest: A tight noisy purification circuit reverses preparation-error monotonicity. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators

namespace D5.S3.Quantum.Codes.PurificationCircuitMonotonicityRefutation

/-- Computational-basis bitstrings on `n` qubits. -/
def State (n : ℕ) := Fin n → Bool

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
  | .toffoli control₁ control₂ target _, state =>
      Function.update state target
        (if state control₁ && state control₂ then !state target else state target)

private def stateWeight {n : ℕ} (state : State n) : ℕ :=
  (Finset.univ.filter (fun i => state i)).card

private def idealRun {n : ℕ} : List (Gate n) → State n → State n
  | [], state => state
  | gate :: circuit, state => idealRun circuit (idealAction gate state)

/-- The ideal circuit clears all nominated output bits on all inputs of weight at most `e`. -/
def IsPurification {n : ℕ} (circuit : List (Gate n)) (outputs : Finset (Fin n)) (e : ℕ) : Prop :=
  ∀ state, stateWeight state ≤ e → ∀ i ∈ outputs, idealRun circuit state i = false

private def ProbabilityVector (n : ℕ) := State n → ℝ

private def initialDistribution {n : ℕ} (p0 : ℝ) : ProbabilityVector n :=
  fun state => ∏ i : Fin n, if state i then p0 else 1 - p0

private def depolarize {n : ℕ} (qubits : Finset (Fin n)) (p : ℝ)
    (distribution : ProbabilityVector n) : ProbabilityVector n :=
  fun state =>
    (1 - p) * distribution state +
      p / (2 ^ qubits.card : ℝ) *
        ∑ other in Finset.univ.filter (fun candidate =>
          ∀ i, i ∉ qubits → candidate i = state i), distribution other

private def idleNoise {n : ℕ} : List (Fin n) → ℝ → ProbabilityVector n → ProbabilityVector n
  | [], _, distribution => distribution
  | qubit :: qubits, p, distribution =>
      idleNoise qubits p (depolarize {qubit} p distribution)

private def permute {n : ℕ} (gate : Gate n)
    (distribution : ProbabilityVector n) : ProbabilityVector n :=
  fun state => distribution (idealAction gate state)

private def noisyStep {n : ℕ} (pI pC pT : ℝ) (gate : Gate n)
    (distribution : ProbabilityVector n) : ProbabilityVector n :=
  let gateProbability := match gate with
    | .cnot _ _ _ => pC
    | .toffoli _ _ _ _ _ _ => pT
  let afterGate := depolarize (gateSet gate) gateProbability (permute gate distribution)
  idleNoise (Finset.univ \ gateSet gate).toList pI afterGate

private def noisyRun {n : ℕ} (p0 pI pC pT : ℝ) : List (Gate n) → ProbabilityVector n
  | [] => initialDistribution p0
  | gate :: circuit => noisyStep pI pC pT gate (noisyRun p0 pI pC pT circuit)

/-- Expected fraction of nominated output bits that are true. -/
def pOut {n : ℕ} (p0 pI pC pT : ℝ) (circuit : List (Gate n))
    (outputs : Finset (Fin n)) : ℝ :=
  (∑ i in outputs, ∑ state, if state i then noisyRun p0 pI pC pT circuit state else 0) /
    (outputs.card : ℝ)

private def admissible (p0 pI pC pT : ℝ) : Prop :=
  0 ≤ p0 ∧ p0 < 1 / 2 ∧ 0 ≤ pI ∧ pI ≤ 1 ∧ 0 ≤ pC ∧ pC ≤ 1 ∧ 0 ≤ pT ∧ pT ≤ 1

/-- The source question's coordinatewise monotonicity assertion. -/
def claim : Prop :=
  ∀ (n k e : ℕ) (circuit : List (Gate n)) (outputs : Finset (Fin n)),
    1 ≤ k → k ≤ n → outputs.card = k → IsPurification circuit outputs e →
      (∑ j in Finset.range (e + 1), n.choose j) = 2 ^ (n - k) →
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

private lemma witness_purification :
    IsPurification
      ([Gate.cnot 0 1 (by decide), Gate.cnot 1 2 (by decide),
        Gate.cnot 1 0 (by decide), Gate.cnot 0 2 (by decide),
        Gate.cnot 1 0 (by decide), Gate.toffoli 1 2 0 (by decide) (by decide) (by decide)] :
          List (Gate 3)) {0} 1 := by
  sorry

private lemma witness_space :
    (∑ j in Finset.range (1 + 1), 3.choose j) = 2 ^ (3 - 1) := by
  norm_num [Nat.choose]

private lemma witness_evaluation_zero :
    pOut 0 0 (1 / 4) 0
      ([Gate.cnot 0 1 (by decide), Gate.cnot 1 2 (by decide),
        Gate.cnot 1 0 (by decide), Gate.cnot 0 2 (by decide),
        Gate.cnot 1 0 (by decide), Gate.toffoli 1 2 0 (by decide) (by decide) (by decide)] :
          List (Gate 3)) {0} = 1481 / 4096 := by
  sorry

private lemma witness_evaluation_small :
    pOut (1 / 100) 0 (1 / 4) 0
      ([Gate.cnot 0 1 (by decide), Gate.cnot 1 2 (by decide),
        Gate.cnot 1 0 (by decide), Gate.cnot 0 2 (by decide),
        Gate.cnot 1 0 (by decide), Gate.toffoli 1 2 0 (by decide) (by decide) (by decide)] :
          List (Gate 3)) {0} = 23121347 / 64000000 := by
  sorry

theorem result : ¬ claim := by
  sorry

end D5.S3.Quantum.Codes.PurificationCircuitMonotonicityRefutation
