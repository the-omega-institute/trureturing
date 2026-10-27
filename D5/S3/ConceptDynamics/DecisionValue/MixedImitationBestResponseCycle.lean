/- GID: D5/S3/ConceptDynamics/DecisionValue/MixedImitationBestResponseCycle
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/DecisionValue/MixedImitationBestResponseCycle
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/ConceptDynamics/DecisionValue/MixedImitationBestResponseCycle.claim; result=D5/S3/ConceptDynamics/DecisionValue/MixedImitationBestResponseCycle.result; claim=D5/S3/ConceptDynamics/DecisionValue/MixedImitationBestResponseCycle.claim
   digest: A persistent mixed imitation and best-response trajectory never reaches equilibrium. -/

import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Periodic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

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
    Symmetric adj → Std.Irrefl adj →
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
  ![2, 0, 3, 1] (Fin.ofNat 4 t)

private theorem graph_symmetric : Symmetric graph := by
  intro i j h
  rcases h with ⟨hne, hgap⟩
  refine ⟨Ne.symm hne, ?_⟩
  rintro (⟨hzero, htwo⟩ | ⟨htwo, hzero⟩)
  · exact hgap (Or.inr ⟨htwo, hzero⟩)
  · exact hgap (Or.inl ⟨hzero, htwo⟩)

private theorem graph_irreflexive : Std.Irrefl graph := by
  refine ⟨?_⟩
  intro i h
  exact h.1 rfl

private theorem payoffs_coordination : ∀ i,
    max (payoffs i true false) (payoffs i false true) <
      min (payoffs i false false) (payoffs i true true) := by
  intro i
  fin_cases i <;> dsimp only [payoffs] <;> norm_num

private theorem activation_persistent : IsPersistent activation := by
  intro i t
  fin_cases i
  · refine ⟨4 * t + 1, by omega, ?_⟩
    dsimp only [activation, Fin.ofNat]
    norm_num [Nat.add_mod, Nat.mul_mod]
  · refine ⟨4 * t + 3, by omega, ?_⟩
    dsimp only [activation, Fin.ofNat]
    norm_num [Nat.add_mod, Nat.mul_mod]
  · refine ⟨4 * t, by omega, ?_⟩
    dsimp only [activation, Fin.ofNat]
    norm_num [Nat.mul_mod]
  · refine ⟨4 * t + 2, by omega, ?_⟩
    dsimp only [activation, Fin.ofNat]
    norm_num [Nat.add_mod, Nat.mul_mod]

private theorem activation_period (t : ℕ) : activation (t + 8) = activation t := by
  unfold activation
  exact congrArg (![2, 0, 3, 1] : Fin 4 → Fin 4) (Fin.ext (Nat.add_mul_mod_self_left t 4 2))

private theorem utility_values (r : Fin 8) (i : Fin 4) :
    utility graph payoffs (orbit r) i =
      (![![4, 6, 4, 11], ![0, 7, 0, 10], ![4, 8, 4, 9], ![4, 7, 5, 10],
        ![1, 6, 5, 11], ![0, 7, 2, 10], ![1, 8, 5, 9], ![1, 7, 4, 10]] :
          Fin 8 → Fin 4 → ℝ) r i := by
  fin_cases r <;> fin_cases i <;> unfold utility
  all_goals simp only [Finset.sum_filter, Fin.sum_univ_succ, Fin.sum_univ_zero]
  all_goals dsimp only [graph, payoffs, orbit]
  all_goals norm_num

private theorem alternative_values (r : Fin 8) (s : Bool) :
    utility graph payoffs (Function.update (orbit r) 1 s) 1 =
      (if s then (![9, 8, 8, 7, 6, 7, 7, 8] : Fin 8 → ℝ)
        else ![6, 7, 7, 8, 9, 8, 8, 7]) r := by
  fin_cases r <;> cases s <;> unfold utility
  all_goals rw [Finset.sum_filter]
  all_goals simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Function.update_apply]
  all_goals dsimp only [graph, payoffs, orbit]
  all_goals norm_num

private theorem first_two :
    step graph kinds payoffs (orbit 0) (activation 0) = orbit 0 ∧
    step graph kinds payoffs (orbit 0) (activation 1) = orbit 0 := by
  classical
  constructor
  all_goals
    unfold activation Fin.ofNat
    norm_num only
    unfold step update
    dsimp only [kinds]
    norm_num
    try dsimp only [hasMaximizer]
    simp only [utility_values]
    dsimp only [graph, orbit]
    norm_num [Fin.exists_fin_succ, Fin.forall_fin_succ]

private theorem cycle_steps (r : Fin 8) :
    step graph kinds payoffs (orbit r) (activation (r.val + 2)) =
      orbit ⟨(r.val + 1) % 8, Nat.mod_lt _ (by decide)⟩ := by
  classical
  fin_cases r
  all_goals
    unfold activation Fin.ofNat
    norm_num only
    unfold step update
    dsimp only [kinds]
    norm_num
    try dsimp only [hasMaximizer]
    simp only [utility_values, alternative_values]
    dsimp only [graph, orbit]
    norm_num [Fin.exists_fin_succ, Fin.forall_fin_succ]
    funext i
    fin_cases i <;> simp

private theorem first_ten (t : ℕ) (ht : t ≤ 10) :
    traj graph kinds payoffs (orbit 0) activation t =
      if t < 2 then orbit 0 else orbit ⟨(t - 2) % 8, Nat.mod_lt _ (by decide)⟩ := by
  obtain ⟨hzero, hone⟩ := first_two
  have h0 : step graph kinds payoffs (orbit 0) (activation 2) =
      orbit 1 := cycle_steps 0
  have h1 : step graph kinds payoffs (orbit 1) (activation 3) =
      orbit 2 := cycle_steps 1
  have h2 : step graph kinds payoffs (orbit 2) (activation 4) =
      orbit 3 := cycle_steps 2
  have h3 : step graph kinds payoffs (orbit 3) (activation 5) =
      orbit 4 := cycle_steps 3
  have h4 : step graph kinds payoffs (orbit 4) (activation 6) =
      orbit 5 := cycle_steps 4
  have h5 : step graph kinds payoffs (orbit 5) (activation 7) =
      orbit 6 := cycle_steps 5
  have h6 : step graph kinds payoffs (orbit 6) (activation 8) =
      orbit 7 := cycle_steps 6
  have h7 : step graph kinds payoffs (orbit 7) (activation 9) =
      orbit 0 := cycle_steps 7
  have hcases : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨
      t = 7 ∨ t = 8 ∨ t = 9 ∨ t = 10 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals dsimp only [traj]
  all_goals norm_num [hzero, hone, h0, h1, h2, h3, h4, h5, h6, h7]

private theorem trajectory_period (t : ℕ) (ht : 2 ≤ t) :
    traj graph kinds payoffs (orbit 0) activation (t + 8) =
      traj graph kinds payoffs (orbit 0) activation t := by
  induction t with
  | zero => omega
  | succ t ih =>
    by_cases hsmall : t < 2
    · have heq : t = 1 := by omega
      subst t
      rw [first_ten 10 (by omega), first_ten 2 (by omega)]
      rfl
    · change step graph kinds payoffs
        (traj graph kinds payoffs (orbit 0) activation (t + 8)) (activation (t + 8)) =
          step graph kinds payoffs (traj graph kinds payoffs (orbit 0) activation t)
            (activation t)
      rw [activation_period]
      exact congrArg (fun x => traj._sunfold graph kinds payoffs x
        (fun _ => activation t) 1) (ih (by omega))

private theorem trajectory_reduce (t : ℕ) :
    traj graph kinds payoffs (orbit 0) activation (t + 2) =
      traj graph kinds payoffs (orbit 0) activation (t % 8 + 2) := by
  have hp : Function.Periodic
      (fun k => traj graph kinds payoffs (orbit 0) activation (k + 2)) 8 := by
    intro k
    exact trajectory_period (k + 2) (by omega)
  exact (hp.map_mod_nat t).symm

private theorem equilibrium_step {n : ℕ} (adj : Fin n → Fin n → Prop)
    (imitator : Fin n → Bool) (pay : Fin n → Bool → Bool → ℝ)
    (x : Fin n → Bool) (h : IsEquilibrium adj imitator pay x) (i : Fin n) :
    step adj imitator pay x i = x := by
  exact h (fun _ => i) 1

private theorem orbit_not_equilibrium (r : Fin 8) :
    ¬ IsEquilibrium graph kinds payoffs (orbit r) := by
  intro h
  have hfixed := equilibrium_step graph kinds payoffs (orbit r) h (activation (r.val + 2))
  have hmoved : orbit r ≠ orbit ⟨(r.val + 1) % 8, Nat.mod_lt _ (by decide)⟩ := by
    fin_cases r <;> decide
  exact hmoved (hfixed.symm.trans (cycle_steps r))

private theorem never_equilibrium (t : ℕ) :
    ¬ IsEquilibrium graph kinds payoffs (traj graph kinds payoffs (orbit 0) activation t) := by
  by_cases hsmall : t < 2
  · rw [first_ten t (by omega), ite_eq_left hsmall]
    exact orbit_not_equilibrium 0
  · have heq : t = (t - 2) + 2 := by omega
    rw [heq, trajectory_reduce]
    rw [first_ten ((t - 2) % 8 + 2) (by omega), ite_eq_right (by omega)]
    exact orbit_not_equilibrium _

/-- A four-agent network disproves equilibration under every persistent sequence. -/
theorem result : ¬ claim := by
  intro h
  obtain ⟨t, ht⟩ := h 4 graph graph_symmetric graph_irreflexive kinds payoffs
    payoffs_coordination (orbit 0) activation activation_persistent
  exact never_equilibrium t ht

end D5.S3.ConceptDynamics.DecisionValue.MixedImitationBestResponseCycle
