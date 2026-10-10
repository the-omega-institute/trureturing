/- GID: D5/S3/ConceptDynamics/Control/CalibrationHistoryCoarsestQuotient
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Control/CalibrationHistoryCoarsestQuotient
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/ConceptDynamics/Control/CalibrationHistoryCoarsestQuotient.claim; result=D5/S3/ConceptDynamics/Control/CalibrationHistoryCoarsestQuotient.refutation; claim=D5/S3/ConceptDynamics/Control/CalibrationHistoryCoarsestQuotient.claim
   digest: Pairwise solvable destructive calibration histories have no coarsest feasible encoding. -/

import D5.S3.ConceptDynamics.Control.FiniteHorizonReachability
import Mathlib.Data.Fintype.Quotient
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Setoid.Basic
import Mathlib.Tactic.FinCases
import Mathlib.SetTheory.Cardinal.Finite

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

namespace D5.S3.ConceptDynamics.Control.CalibrationHistoryCoarsestQuotient

open D5.S3.ConceptDynamics.Control.FiniteHorizonReachability

/-- A bad set closed against every control choice excludes every bounded strategy. -/
private theorem trap_general {X : Type*} (system : ControlSystem X)
    (goal bad : Set X)
    (apart : ∀ x ∈ bad, x ∉ goal)
    (trapped : ∀ x ∈ bad, ∀ action : system.Action x,
      ∃ next ∈ system.successor action, next ∈ bad)
    {n : ℕ} {x : X} (hx : x ∈ bad) :
    ¬ BoundedReachStrategy system goal n x := by
  intro strategy
  induction strategy with
  | now atGoal => exact apart _ hx atGoal
  | step action continuation ih =>
      obtain ⟨next, attained, stays⟩ := trapped _ hx action
      exact ih next attained stays

/-- The only live information is the set of possible calibration histories.
After an experiment, either a bit is known or both bits share the dead record. -/
inductive Cell where
  | live (histories : {s : Set (Fin 3) // s.Nonempty})
  | known (bit : Bool)
  | dead

/-- Experiments are indexed by their failing history: 0 is c, 1 is a, 2 is b. -/
def response (history : Fin 3) (bit : Bool) (experiment : Fin 3) : Option Bool :=
  if history = experiment then none else some bit

/-- The nonempty response fiber after destructive measurement. -/
def postResponse : Option Bool → Cell
  | none => .dead
  | some bit => .known bit

/-- The possible retained targets; live and failed cells both contain both bits. -/
def possibleTargets : Cell → Set Bool
  | .known bit => {bit}
  | _ => Set.univ

/-- A known bit permits stopping. Live and dead cells do not. -/
def goal : Set Cell := {cell | ∃ bit, cell = .known bit}

/-- Every live experiment destroys the device. Later experiments cannot refine
its surviving target candidates. Successors are the attained response fibers. -/
def calibrationSystem : ControlSystem Cell where
  Action _ := Fin 3
  successor := fun {cell} experiment => match cell with
    | .live histories => {next | ∃ i ∈ histories.val, ∃ bit,
        next = postResponse (response i bit experiment)}
    | .known bit => {next | next = .known bit}
    | .dead => {next | next = .dead}
  successor_nonempty := by
    intro cell experiment
    cases cell with
    | live histories =>
        obtain ⟨i, member⟩ := histories.property
        exact ⟨postResponse (response i false experiment), i, member, false, rfl⟩
    | known bit => exact ⟨.known bit, rfl⟩
    | dead => exact ⟨.dead, rfl⟩

/-- An encoding is feasible when every one of its history classes admits a
strategy within the common horizon. The merger is fixed independently of it. -/
def TaskFeasible {H X : Type*} (system : ControlSystem X) (target : Set X)
    (merge : {s : Set H // s.Nonempty} → X) (n : ℕ) (encoding : Setoid H) : Prop :=
  ∀ i, BoundedReachStrategy system target n
    (merge ⟨{j | encoding i j}, i, encoding.refl i⟩)

/-- The assertion that every feasible history task has a feasible encoding
coarser than every feasible encoding, for every positive finite budget. -/
def claim : Prop :=
  ∀ (H X : Type) (system : ControlSystem.{0, 0} X) (target : Set X)
    (merge : {s : Set H // s.Nonempty} → X) (n : ℕ),
    1 ≤ n → (∃ encoding, TaskFeasible system target merge n encoding) →
      ∃ encoding, TaskFeasible system target merge n encoding ∧
        ∀ other, TaskFeasible system target merge n other → other ≤ encoding

private theorem dead_no_strategy (n : ℕ) :
    ¬ BoundedReachStrategy calibrationSystem goal n .dead := by
  apply trap_general calibrationSystem goal {Cell.dead}
  · intro cell hc
    subst cell
    rintro ⟨bit, equal⟩
    cases equal
  · intro cell hc experiment
    subst cell
    exact ⟨.dead, rfl, rfl⟩
  · rfl

private theorem live_no_zero (histories : {s : Set (Fin 3) // s.Nonempty}) :
    ¬ BoundedReachStrategy calibrationSystem goal 0 (.live histories) := by
  intro strategy
  have atGoal :=
    (finite_horizon_reachability calibrationSystem goal 0 (.live histories)).mpr strategy
  obtain ⟨bit, equal⟩ := atGoal
  cases equal

private theorem full_no_strategy (n : ℕ) :
    ¬ BoundedReachStrategy calibrationSystem goal n
      (.live ⟨Set.univ, 0, Set.mem_univ 0⟩) := by
  intro strategy
  cases strategy with
  | now atGoal =>
      obtain ⟨bit, equal⟩ := atGoal
      cases equal
  | step experiment continuation =>
      change Fin 3 at experiment
      apply dead_no_strategy _ (continuation .dead ?_)
      exact ⟨experiment, Set.mem_univ experiment, false, by
        simp [response, postResponse]⟩

private theorem avoiding_one_step
    (histories : {s : Set (Fin 3) // s.Nonempty})
    (experiment : Fin 3) (avoids : experiment ∉ histories.val) (n : ℕ) :
    BoundedReachStrategy calibrationSystem goal (n + 1) (.live histories) := by
  refine .step experiment ?_
  intro next attained
  obtain ⟨i, member, bit, equal⟩ := attained
  have different : i ≠ experiment := ne_of_mem_of_not_mem member avoids
  simp only [response, if_neg different, postResponse] at equal
  exact .now ⟨bit, equal⟩

local notation "P12" => Setoid.ker (fun i : Fin 3 => decide (i = 2))
local notation "P13" => Setoid.ker (fun i : Fin 3 => decide (i = 1))

private theorem pairs_one_step (i j : Fin 3) (n : ℕ) :
    BoundedReachStrategy calibrationSystem goal (n + 1)
      (.live ⟨{i, j}, i, Or.inl rfl⟩) := by
  fin_cases i <;> fin_cases j <;>
    first
    | exact avoiding_one_step _ 0 (by decide) n
    | exact avoiding_one_step _ 1 (by decide) n
    | exact avoiding_one_step _ 2 (by decide) n

private theorem partitions_feasible (n : ℕ) (positive : 1 ≤ n) :
    TaskFeasible calibrationSystem goal Cell.live n P12 ∧
    TaskFeasible calibrationSystem goal Cell.live n P13 := by
  cases n with
  | zero => cases positive
  | succ n =>
      constructor
      · intro i
        fin_cases i
        · convert pairs_one_step 0 1 n using 1
          congr 2
          ext j
          fin_cases j <;> simp
        · convert pairs_one_step 0 1 n using 1
          congr 2
          ext j
          fin_cases j <;> simp
        · convert pairs_one_step 2 2 n using 1
          congr 2
          ext j
          fin_cases j <;> simp
      · intro i
        fin_cases i
        · convert pairs_one_step 0 2 n using 1
          congr 2
          ext j
          fin_cases j <;> simp
        · convert pairs_one_step 1 1 n using 1
          congr 2
          ext j
          fin_cases j <;> simp
        · convert pairs_one_step 0 2 n using 1
          congr 2
          ext j
          fin_cases j <;> simp

private theorem partition_card : Nat.card (Quotient P12) = 2 := by
  have inverse : Function.RightInverse
      (fun b : Bool => if b then (2 : Fin 3) else 0)
      (fun i : Fin 3 => decide (i = 2)) := by
    intro b
    cases b <;> decide
  rw [Nat.card_congr (Setoid.quotientKerEquivOfRightInverse (fun i : Fin 3 => decide (i = 2)) _ inverse)]
  simp

private theorem feasible_card_lower (n : ℕ) (encoding : Setoid (Fin 3))
    (feasible : TaskFeasible calibrationSystem goal Cell.live n encoding) :
    2 ≤ Nat.card (Quotient encoding) := by
  by_contra small
  let : Fintype (Quotient encoding) := Fintype.ofFinite _
  have subsingleton : Subsingleton (Quotient encoding) :=
    Fintype.card_le_one_iff_subsingleton.mp (by
      simpa only [Nat.card_eq_fintype_card] using
        Nat.le_of_lt_succ (Nat.lt_of_not_ge small))
  have fullClass : {j | encoding 0 j} = (Set.univ : Set (Fin 3)) :=
    Set.eq_univ_of_forall
      (Setoid.eq_top_iff.mp (Quotient.subsingleton_iff.mp subsingleton) 0)
  exact full_no_strategy n (by simpa only [fullClass] using feasible 0)

private theorem no_coarsest (n : ℕ) (positive : 1 ≤ n) :
    ¬ ∃ encoding, TaskFeasible calibrationSystem goal Cell.live n encoding ∧
      ∀ other, TaskFeasible calibrationSystem goal Cell.live n other →
        other ≤ encoding := by
  rintro ⟨encoding, feasible, coarser⟩
  obtain ⟨first, second⟩ := partitions_feasible n positive
  have related01 : encoding 0 1 := coarser P12 first rfl
  have related02 : encoding 0 2 := coarser P13 second rfl
  have fullClass : {j | encoding 0 j} = (Set.univ : Set (Fin 3)) := by
    apply Set.eq_univ_of_forall
    intro j
    fin_cases j
    · exact encoding.refl 0
    · exact related01
    · exact related02
  exact full_no_strategy n (by simpa only [fullClass] using feasible 0)

/-- A typed refutation of universal coarsest task-sufficient encodings. -/
private theorem refutation : ¬ claim := by
  intro universal
  exact no_coarsest 1 (by decide)
    (universal (Fin 3) Cell calibrationSystem goal Cell.live 1 (by decide)
      ⟨P12, (partitions_feasible 1 (by decide)).1⟩)

/-- Single histories and pairs need exactly one step; the full union fails at
all depths. Every positive horizon has minimum two history classes, but no
feasible encoding coarser than all feasible encodings. -/
theorem result :
    (∀ i : Fin 3,
      BoundedReachStrategy calibrationSystem goal 1 (.live ⟨{i}, i, rfl⟩) ∧
      ¬ BoundedReachStrategy calibrationSystem goal 0 (.live ⟨{i}, i, rfl⟩)) ∧
    (∀ i j : Fin 3,
      BoundedReachStrategy calibrationSystem goal 1 (.live ⟨{i, j}, i, Or.inl rfl⟩) ∧
      ¬ BoundedReachStrategy calibrationSystem goal 0 (.live ⟨{i, j}, i, Or.inl rfl⟩)) ∧
    (∀ n : ℕ, ¬ BoundedReachStrategy calibrationSystem goal n
      (.live ⟨Set.univ, 0, Set.mem_univ 0⟩)) ∧
    (∀ i : Fin 3, possibleTargets (.live ⟨{i}, i, rfl⟩) = Set.univ) ∧
    (∀ n : ℕ, 1 ≤ n →
      (∃ encoding, TaskFeasible calibrationSystem goal Cell.live n encoding ∧
        Nat.card (Quotient encoding) = 2) ∧
      (∀ encoding, TaskFeasible calibrationSystem goal Cell.live n encoding →
        2 ≤ Nat.card (Quotient encoding)) ∧
      ¬ ∃ encoding, TaskFeasible calibrationSystem goal Cell.live n encoding ∧
        ∀ other, TaskFeasible calibrationSystem goal Cell.live n other →
          other ≤ encoding) ∧
    ¬ claim := by
  refine ⟨?_, ?_, full_no_strategy, ?_, ?_, refutation⟩
  · intro i
    have same : ({i, i} : Set (Fin 3)) = {i} := Set.insert_eq_of_mem rfl
    have reach := pairs_one_step i i 0
    simp only [same] at reach
    exact ⟨reach, live_no_zero _⟩
  · intro i j
    exact ⟨pairs_one_step i j 0, live_no_zero _⟩
  · intro i
    rfl
  · intro n positive
    exact ⟨⟨P12, (partitions_feasible n positive).1, partition_card⟩,
      feasible_card_lower n, no_coarsest n positive⟩

#print axioms result
#print axioms refutation

end D5.S3.ConceptDynamics.Control.CalibrationHistoryCoarsestQuotient
