/- GID: D5/S3/ConceptDynamics/DecisionValue/MixedImitationBestResponseCycle
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DecisionValue/MixedImitationBestResponseCycle
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/ConceptDynamics/DecisionValue/MixedImitationBestResponseCycle.claim; result=D5/S3/ConceptDynamics/DecisionValue/MixedImitationBestResponseCycle.result; claim=D5/S3/ConceptDynamics/DecisionValue/MixedImitationBestResponseCycle.claim
   digest: A persistent mixed imitation and best-response trajectory never reaches equilibrium. -/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Omega

/-! A periodic trajectory for coordinating imitation and best-response dynamics. -/

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.DecisionValue.MixedImitationBestResponseCycle

/-- The accumulated payoff against the neighbours, with `false` denoting A. -/
noncomputable def utility {n : ℕ} (adj : Fin n → Fin n → Prop)
    (pay : Fin n → Bool → Bool → ℝ) (x : Fin n → Bool) (i : Fin n) : ℝ := by
  classical
  exact ∑ j ∈ Finset.univ.filter (adj i), pay i (x i) (x j)

/-- Some highest-earning neighbour uses strategy `s`. -/
def hasMaximizer {n : ℕ} (adj : Fin n → Fin n → Prop)
    (pay : Fin n → Bool → Bool → ℝ) (x : Fin n → Bool) (i : Fin n) (s : Bool) : Prop :=
  ∃ j, adj i j ∧ x j = s ∧ ∀ k, adj i k → utility adj pay x k ≤ utility adj pay x j

/-- Imitation copies a uniquely maximizing strategy; best response maximizes own
payoff. Both rules keep the current strategy when both strategies maximize.
An imitator with no neighbours also keeps its strategy. -/
noncomputable def update {n : ℕ} (adj : Fin n → Fin n → Prop)
    (imitator : Fin n → Bool) (pay : Fin n → Bool → Bool → ℝ)
    (x : Fin n → Bool) (i : Fin n) : Bool := by
  classical
  exact if imitator i then
    if hasMaximizer adj pay x i false then
      if hasMaximizer adj pay x i true then x i else false
    else if hasMaximizer adj pay x i true then true else x i
  else
    if utility adj pay (Function.update x i false) i <
        utility adj pay (Function.update x i true) i then true
    else if utility adj pay (Function.update x i true) i <
        utility adj pay (Function.update x i false) i then false
    else x i

/-- One asynchronous update changes only the active coordinate. -/
noncomputable def step {n : ℕ} (adj : Fin n → Fin n → Prop)
    (imitator : Fin n → Bool) (pay : Fin n → Bool → Bool → ℝ)
    (x : Fin n → Bool) (i : Fin n) : Fin n → Bool :=
  Function.update x i (update adj imitator pay x i)

/-- The trajectory driven by an arbitrary activation sequence. -/
noncomputable def traj {n : ℕ} (adj : Fin n → Fin n → Prop)
    (imitator : Fin n → Bool) (pay : Fin n → Bool → Bool → ℝ)
    (x : Fin n → Bool) (a : ℕ → Fin n) : ℕ → (Fin n → Bool)
  | 0 => x
  | t + 1 => step adj imitator pay (traj adj imitator pay x a t) (a t)

/-- The source notion of equilibrium quantifies over every activation sequence. -/
def IsEquilibrium {n : ℕ} (adj : Fin n → Fin n → Prop)
    (imitator : Fin n → Bool) (pay : Fin n → Bool → Bool → ℝ) (x : Fin n → Bool) : Prop :=
  ∀ a : ℕ → Fin n, ∀ t, traj adj imitator pay x a t = x

/-- Each agent is activated at arbitrarily late times. -/
def IsPersistent {n : ℕ} (a : ℕ → Fin n) : Prop :=
  ∀ i t, ∃ u ≥ t, a u = i

/-- Every coordinating mixed network equilibrates along every persistent schedule. -/
def claim : Prop :=
  ∀ (n : ℕ) (adj : Fin n → Fin n → Prop),
    Symmetric adj → Irreflexive adj →
    ∀ (imitator : Fin n → Bool) (pay : Fin n → Bool → Bool → ℝ),
      (∀ i, max (pay i true false) (pay i false true) <
        min (pay i false false) (pay i true true)) →
      ∀ (x : Fin n → Bool) (a : ℕ → Fin n), IsPersistent a →
        ∃ t, IsEquilibrium adj imitator pay (traj adj imitator pay x a t)

private def graph (i j : Fin 4) : Prop :=
  i ≠ j ∧ ¬ ((i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0))

private def kinds (i : Fin 4) : Bool := i != 1

private def payoffs (i : Fin 4) (s r : Bool) : ℝ :=
  (![1, 3, 4, 4] : Fin 4 → ℝ) i * (if s = false ∧ r = false then 1 else 0) +
  (![0, 2, 1, 3] : Fin 4 → ℝ) i * (if s = false ∧ r = true then 1 else 0) +
  (![0, 2, 0, 3] : Fin 4 → ℝ) i * (if s = true ∧ r = false then 1 else 0) +
  (![4, 3, 4, 4] : Fin 4 → ℝ) i * (if s = true ∧ r = true then 1 else 0)

private def orbit : Fin 8 → Fin 4 → Bool :=
  ![![true, false, true, true], ![true, false, true, false],
    ![true, true, true, false], ![true, true, false, false],
    ![false, true, false, false], ![false, true, false, true],
    ![false, false, false, true], ![false, false, true, true]]

private def activation (t : ℕ) : Fin 4 :=
  ![2, 0, 3, 1] ⟨t % 4, Nat.mod_lt t (by decide)⟩

private theorem graph_symmetric : Symmetric graph := by
  sorry

private theorem graph_irreflexive : Irreflexive graph := by
  sorry

private theorem payoffs_coordination : ∀ i,
    max (payoffs i true false) (payoffs i false true) <
      min (payoffs i false false) (payoffs i true true) := by
  sorry

private theorem activation_persistent : IsPersistent activation := by
  sorry

private theorem activation_period (t : ℕ) : activation (t + 8) = activation t := by
  sorry

private theorem first_two :
    step graph kinds payoffs (orbit 0) (activation 0) = orbit 0 ∧
    step graph kinds payoffs (orbit 0) (activation 1) = orbit 0 := by
  sorry

private theorem cycle_steps (r : Fin 8) :
    step graph kinds payoffs (orbit r) (activation (r.val + 2)) =
      orbit ⟨(r.val + 1) % 8, Nat.mod_lt _ (by decide)⟩ := by
  sorry

private theorem first_ten (t : ℕ) (ht : t ≤ 10) :
    traj graph kinds payoffs (orbit 0) activation t =
      if t < 2 then orbit 0 else orbit ⟨(t - 2) % 8, Nat.mod_lt _ (by decide)⟩ := by
  sorry

private theorem trajectory_period (t : ℕ) (ht : 2 ≤ t) :
    traj graph kinds payoffs (orbit 0) activation (t + 8) =
      traj graph kinds payoffs (orbit 0) activation t := by
  sorry

private theorem trajectory_reduce (t : ℕ) :
    traj graph kinds payoffs (orbit 0) activation (t + 2) =
      traj graph kinds payoffs (orbit 0) activation (t % 8 + 2) := by
  sorry

private theorem equilibrium_step {n : ℕ} (adj : Fin n → Fin n → Prop)
    (imitator : Fin n → Bool) (pay : Fin n → Bool → Bool → ℝ)
    (x : Fin n → Bool) (h : IsEquilibrium adj imitator pay x) (i : Fin n) :
    step adj imitator pay x i = x := by
  exact h (fun _ => i) 1

private theorem orbit_not_equilibrium (r : Fin 8) :
    ¬ IsEquilibrium graph kinds payoffs (orbit r) := by
  sorry

private theorem never_equilibrium (t : ℕ) :
    ¬ IsEquilibrium graph kinds payoffs (traj graph kinds payoffs (orbit 0) activation t) := by
  sorry

/-- A four-agent network disproves equilibration under every persistent sequence. -/
theorem result : ¬ claim := by
  intro h
  obtain ⟨t, ht⟩ := h 4 graph graph_symmetric graph_irreflexive kinds payoffs
    payoffs_coordination (orbit 0) activation activation_persistent
  exact never_equilibrium t ht

end D5.S3.ConceptDynamics.DecisionValue.MixedImitationBestResponseCycle
