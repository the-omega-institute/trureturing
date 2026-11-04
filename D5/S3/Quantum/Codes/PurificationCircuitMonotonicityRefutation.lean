/- GID: D5/S3/Quantum/Codes/PurificationCircuitMonotonicityRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Codes/PurificationCircuitMonotonicityRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Codes/PurificationCircuitMonotonicityRefutation.claim; result=D5/S3/Quantum/Codes/PurificationCircuitMonotonicityRefutation.result; claim=D5/S3/Quantum/Codes/PurificationCircuitMonotonicityRefutation.claim
   digest: A tight noisy purification circuit reverses preparation-error monotonicity. -/

import D5.S3.Quantum.Entanglement.RandomizedGraphNegativityRefutation
import D5.S3.Entropy.NamingWindow.GreenClassWindowEntropy
import D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationConfidenceFailure

/-! The source error model admits a finite circuit whose output error decreases with preparation error. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators

open D5.S3.Quantum.Entanglement.RandomizedGraphNegativityRefutation (Qubits)
open D5.S3.Entropy.NamingWindow.GreenClassWindowEntropy (windowLaw)
open D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationConfidenceFailure.ScoreBridge
  (bernoulliMass)

namespace D5.S3.Quantum.Codes.PurificationCircuitMonotonicityRefutation

/-- A CNOT or Toffoli gate with the required distinct qubits. -/
abbrev Gate (n : ℕ) :=
  {p : Fin n × Fin n // p.1 ≠ p.2} ⊕
    {p : Fin n × Fin n × Fin n // p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2 ∧ p.2.1 ≠ p.2.2}

/-- The qubits acted on by a gate. -/
def gateSet {n : ℕ} : Gate n → Finset (Fin n) :=
  Sum.elim (fun p => {p.val.1, p.val.2})
    (fun p => {p.val.1, p.val.2.1, p.val.2.2})

private def idealAction {n : ℕ} : Gate n → Qubits n → Qubits n :=
  Sum.elim
    (fun p state => Function.update state p.val.2
      (if state p.val.1 then !state p.val.2 else state p.val.2))
    (fun p state => Function.update state p.val.2.2
      (if state p.val.1 && state p.val.2.1 then !state p.val.2.2 else state p.val.2.2))

private def idealRun {n : ℕ} (circuit : List (Gate n)) (state : Qubits n) : Qubits n :=
  circuit.foldl (fun current gate => idealAction gate current) state

/-- The ideal circuit clears all nominated output bits on all inputs of weight at most `e`. -/
def IsPurification {n : ℕ} (circuit : List (Gate n)) (outputs : Finset (Fin n)) (e : ℕ) : Prop :=
  ∀ state, hammingDist state (fun _ => false) ≤ e → ∀ i ∈ outputs, idealRun circuit state i = false

private def initialDistribution {n : ℕ} (p0 : ℝ) : (Qubits n → ℝ) :=
  windowLaw (fun _ => bernoulliMass p0)

private def depolarize {n : ℕ} (qubits : Finset (Fin n)) (p : ℝ)
    (distribution : (Qubits n → ℝ)) : (Qubits n → ℝ) := by
  classical
  exact fun state =>
    (1 - p) * distribution state +
      p / (2 ^ qubits.card : ℝ) *
        Finset.sum (Finset.univ.filter (fun candidate =>
          ∀ i, i ∉ qubits → candidate i = state i)) (fun other => distribution other)

private def idleNoise {n : ℕ} (qubits : List (Fin n)) (p : ℝ)
    (distribution : (Qubits n → ℝ)) : (Qubits n → ℝ) :=
  qubits.foldl (fun current qubit => depolarize {qubit} p current) distribution

private def permute {n : ℕ} (gate : Gate n)
    (distribution : (Qubits n → ℝ)) : (Qubits n → ℝ) :=
  fun state => distribution (idealAction gate state)

private def noisyStep {n : ℕ} (pI pC pT : ℝ) (gate : Gate n)
    (distribution : (Qubits n → ℝ)) : (Qubits n → ℝ) := by
  classical
  exact
    let gateProbability := Sum.elim (fun _ => pC) (fun _ => pT) gate
    let afterGate := depolarize (gateSet gate) gateProbability (permute gate distribution)
    idleNoise (Finset.univ \ gateSet gate).toList pI afterGate

private def noisyRun {n : ℕ} (p0 pI pC pT : ℝ) (circuit : List (Gate n)) : (Qubits n → ℝ) :=
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
    (distribution : (Qubits n → ℝ)) : depolarize qubits 0 distribution = distribution := by
  funext state
  dsimp only [depolarize]
  simp

private lemma idle_zero {n : ℕ} (qubits : List (Fin n))
    (distribution : (Qubits n → ℝ)) : idleNoise qubits 0 distribution = distribution := by
  induction qubits generalizing distribution with
  | nil => rfl
  | cons qubit qubits ih =>
      change idleNoise qubits 0 (depolarize {qubit} 0 distribution) = distribution
      rw [depolarize_zero]
      exact ih distribution

private lemma state_univ_three :
    (Finset.univ : Finset (Qubits 3)) =
      {![false, false, false], ![false, false, true], ![false, true, false],
        ![false, true, true], ![true, false, false], ![true, false, true],
        ![true, true, false], ![true, true, true]} := by
  ext state
  simp only [Finset.mem_univ, true_iff, Finset.mem_insert, Finset.mem_singleton]
  cases h0 : state 0 <;> cases h1 : state 1 <;> cases h2 : state 2
  all_goals
    have hs : state = ![state 0, state 1, state 2] := (FinVec.etaExpand_eq state).symm
    rw [hs]
    simp [h0, h1, h2]

/-- The source question's coordinatewise monotonicity assertion. -/
def claim : Prop :=
  ∀ (n k e : ℕ) (circuit : List (Gate n)) (outputs : Finset (Fin n)),
    1 ≤ k → k ≤ n → 1 ≤ e → e ≤ n → outputs.card = k → IsPurification circuit outputs e →
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

private lemma weight_ge_two {n : ℕ} (state : Qubits n) (i j : Fin n)
    (hij : i ≠ j) (hi : state i = true) (hj : state j = true) :
    2 ≤ hammingDist state (fun _ => false) := by
  classical
  exact Finset.one_lt_card.mpr
    ⟨i, by simp [hi], j, by simp [hj], hij⟩

private lemma witness_purification :
    IsPurification
      ([Sum.inl ⟨(0, 1), by decide⟩, Sum.inl ⟨(1, 2), by decide⟩,
        Sum.inl ⟨(1, 0), by decide⟩, Sum.inl ⟨(0, 2), by decide⟩,
        Sum.inl ⟨(1, 0), by decide⟩, Sum.inr ⟨(1, 2, 0), by decide⟩] :
          List (Gate 3)) {0} 1 := by
  intro state hweight i hi
  have hi0 : i = 0 := by simpa using hi
  subst i
  cases h0 : state 0 <;> cases h1 : state 1 <;> cases h2 : state 2
  · dsimp only [idealRun, idealAction]
    norm_num [h0, h1, h2]
  · dsimp only [idealRun, idealAction]
    norm_num [h0, h1, h2]
  · dsimp only [idealRun, idealAction]
    norm_num [h0, h1, h2]
  · have hbad := weight_ge_two state 1 2 (by decide) h1 h2
    exfalso
    exact Nat.not_lt_of_ge hbad (Nat.lt_succ_of_le hweight)
  · dsimp only [idealRun, idealAction]
    norm_num [h0, h1, h2]
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
      ([Sum.inl ⟨(0, 1), by decide⟩, Sum.inl ⟨(1, 2), by decide⟩,
        Sum.inl ⟨(1, 0), by decide⟩, Sum.inl ⟨(0, 2), by decide⟩,
        Sum.inl ⟨(1, 0), by decide⟩, Sum.inr ⟨(1, 2, 0), by decide⟩] :
          List (Gate 3)) {0} = 1481 / 4096 := by
  dsimp only [pOut, noisyRun, noisyStep, permute, idealAction, gateSet, List.foldl]
  simp only [idle_zero]
  dsimp only [depolarize, permute, idealAction, initialDistribution, windowLaw, bernoulliMass]
  norm_num (config := { maxSteps := 1000000 }) [state_univ_three,
    Fin.forall_fin_succ, Fin.prod_univ_succ, Finset.sum_filter, Function.update_apply]

set_option maxHeartbeats 4000000 in
-- The finite six-round probability reduction requires the enlarged kernel budget.
private lemma witness_evaluation_small :
    pOut (1 / 100) 0 (1 / 4) 0
      ([Sum.inl ⟨(0, 1), by decide⟩, Sum.inl ⟨(1, 2), by decide⟩,
        Sum.inl ⟨(1, 0), by decide⟩, Sum.inl ⟨(0, 2), by decide⟩,
        Sum.inl ⟨(1, 0), by decide⟩, Sum.inr ⟨(1, 2, 0), by decide⟩] :
          List (Gate 3)) {0} = 23121347 / 64000000 := by
  dsimp only [pOut, noisyRun, noisyStep, permute, idealAction, gateSet, List.foldl]
  simp only [idle_zero]
  dsimp only [depolarize, permute, idealAction, initialDistribution, windowLaw, bernoulliMass]
  norm_num (config := { maxSteps := 1000000 }) [state_univ_three,
    Fin.forall_fin_succ, Fin.prod_univ_succ, Finset.sum_filter, Function.update_apply]

theorem result : ¬ claim := by
  intro hclaim
  have hmono :=
    (hclaim 3 1 1
      ([Sum.inl ⟨(0, 1), by decide⟩, Sum.inl ⟨(1, 2), by decide⟩,
        Sum.inl ⟨(1, 0), by decide⟩, Sum.inl ⟨(0, 2), by decide⟩,
        Sum.inl ⟨(1, 0), by decide⟩, Sum.inr ⟨(1, 2, 0), by decide⟩] :
          List (Gate 3)) {0}
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      witness_purification witness_space).1
  have hzero : admissible (0 : ℝ) 0 (1 / 4) 0 := by
    dsimp only [admissible]
    norm_num
  have hsmall : admissible (1 / 100 : ℝ) 0 (1 / 4) 0 := by
    dsimp only [admissible]
    norm_num
  have hineq := hmono 0 0 (1 / 4) 0 (1 / 100) 0 (1 / 4) 0
    hzero hsmall (by norm_num) rfl rfl rfl
  rw [witness_evaluation_zero, witness_evaluation_small] at hineq
  norm_num at hineq

end D5.S3.Quantum.Codes.PurificationCircuitMonotonicityRefutation
