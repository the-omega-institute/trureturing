/- GID: D5/S3/ConceptDynamics/Causal/SoftInterventionModularity
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Causal/SoftInterventionModularity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite products split locally; linked changes break it; empty/singleton cases pass. -/
/- Library-search audit trail (2026-08-29): searched `ProbabilityTheory.Kernel`, `PMF`,
   `Finset.prod`, `Finset.prod_congr`, and `MeasureTheory.Measure.bind`. `PMF` and
   `Finset.prod_ite` are used below; no exact repository theorem for DAG mechanism modules,
   soft intervention, or the local replacement formula was found. The existing
   `ThreeLayerCausalObservationLanguage` module defines action-indexed law profiles, not
   finite DAG kernels, so it is not reused. -/

import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Causal.SoftInterventionModularity

open scoped BigOperators
noncomputable section

/-- A finite DAG is represented by parent finsets ordered by the node index. -/
structure FiniteDAG (n : Nat) where
  parents : Fin n → Finset (Fin n)
  parent_lt : ∀ {child parent}, parent ∈ parents child → parent < child

abbrev State (n m : Nat) := Fin n → Fin m

/- Definition 266.1: a parent-indexed finite kernel family on a finite DAG. -/
def mechanismModule {n : Nat} (dag : FiniteDAG n) (m : Nat) :=
  (v : Fin n) → (dag.parents v → Fin m) → PMF (Fin m)

/- Definition 266.2: replace the kernels at exactly the selected nodes. -/
def softIntervention {n : Nat} (dag : FiniteDAG n) (m : Nat)
    (base : mechanismModule dag m) (selected : Finset (Fin n))
    (replacement : mechanismModule dag m) : mechanismModule dag m :=
  fun v parentValues =>
    if v ∈ selected then replacement v parentValues else base v parentValues

/-- The finite joint mass obtained by multiplying the local mechanism masses. -/
def jointLaw {n : Nat} (dag : FiniteDAG n) (m : Nat)
    (kernels : mechanismModule dag m) (state : State n m) : ENNReal :=
  ∏ v : Fin n, kernels v (fun parent => state parent.1) (state v)

/-- The joint mass is the selected replacement product times the unchanged product. -/
theorem local_replacement_formula
    {n : Nat} (dag : FiniteDAG n) (m : Nat) (base replacement : mechanismModule dag m)
    (selected : Finset (Fin n)) (state : State n m) :
    jointLaw dag m (softIntervention dag m base selected replacement) state =
      (∏ i ∈ selected,
        replacement i (fun parent => state parent.1) (state i)) *
      (∏ v ∈ Finset.univ \ selected,
        base v (fun parent => state parent.1) (state v)) := by
  calc
    jointLaw dag m (softIntervention dag m base selected replacement) state =
        ∏ x : Fin n, if x ∈ selected then
          replacement x (fun parent => state parent.1) (state x)
        else base x (fun parent => state parent.1) (state x) := by
      unfold jointLaw
      apply Finset.prod_congr rfl
      intro x hx
      by_cases h : x ∈ selected
      · simp [softIntervention, h]
      · simp [softIntervention, h]
    _ = (∏ i ∈ selected,
        replacement i (fun parent => state parent.1) (state i)) *
        (∏ v ∈ Finset.univ \ selected,
          base v (fun parent => state parent.1) (state v)) := by
      rw [Finset.prod_ite]
      simp [Finset.filter_notMem_eq_sdiff]

#print axioms local_replacement_formula

private def twoNodeDag : FiniteDAG 2 where
  parents := fun v => if v = 0 then ∅ else {0}
  parent_lt := by
    intro child parent h
    fin_cases child
    · simp at h
    · have hp : parent = 0 := by simpa using h
      subst parent
      decide

private def baseTwoNodeModule : mechanismModule twoNodeDag 2 :=
  fun _ _ => PMF.pure 0

private def linkedTwoNodeModule : mechanismModule twoNodeDag 2 :=
  fun _ _ => PMF.pure 1

private def rootOnlyReplacement : mechanismModule twoNodeDag 2 :=
  fun v _ => if v = 0 then PMF.pure 1 else PMF.pure 0

private def rootIntervention : Finset (Fin 2) := {0}

private def allFalseState : State 2 2 := fun _ => 0

private def allTrueState : State 2 2 := fun _ => 1

/-- A linked device changes both the root and child mechanisms, so the local formula fails. -/
theorem modularity_is_necessary :
    jointLaw twoNodeDag 2 linkedTwoNodeModule allTrueState ≠
      (∏ i ∈ rootIntervention,
        rootOnlyReplacement i (fun parent => allTrueState parent.1) (allTrueState i)) *
      (∏ v ∈ Finset.univ \ rootIntervention,
        baseTwoNodeModule v (fun parent => allTrueState parent.1) (allTrueState v)) := by
  have hcard : (Finset.univ \ rootIntervention : Finset (Fin 2)).card = 1 := by
    decide
  have hcard' : (Finset.univ \ ({0} : Finset (Fin 2))).card = 1 := by
    decide
  norm_num [jointLaw, linkedTwoNodeModule, rootOnlyReplacement, rootIntervention,
    baseTwoNodeModule, allTrueState, twoNodeDag, hcard, hcard']

#print axioms modularity_is_necessary

/- Degenerate audits: no intervention, all nodes replaced, self replacement, one node,
   edgeless DAG, and the empty node type. -/
private def oneNodeDag : FiniteDAG 1 where
  parents := fun _ => ∅
  parent_lt := by simp

private def emptyDag : FiniteDAG 0 where
  parents := fun v => Fin.elim0 v
  parent_lt := by
    intro child
    exact Fin.elim0 child

private def identityOneState : State 1 1 := fun x => x

private def zeroOneState : State 1 1 := fun _ => 0

example {n : Nat} (dag : FiniteDAG n) (m : Nat) (base : mechanismModule dag m)
    (state : State n m) :
    jointLaw dag m (softIntervention dag m base ∅ base) state = jointLaw dag m base state := by
  simp [jointLaw, softIntervention]

example {n : Nat} (dag : FiniteDAG n) (m : Nat) (base replacement : mechanismModule dag m)
    (state : State n m) :
    jointLaw dag m (softIntervention dag m base Finset.univ replacement) state =
      ∏ i : Fin n, replacement i (fun parent => state parent.1) (state i) := by
  simp [jointLaw, softIntervention]

example {n : Nat} (dag : FiniteDAG n) (m : Nat) (base : mechanismModule dag m)
    (selected : Finset (Fin n)) (state : State n m) :
    jointLaw dag m (softIntervention dag m base selected base) state =
      jointLaw dag m base state := by
  simp [jointLaw, softIntervention]

example :
    jointLaw oneNodeDag 1 (fun _ _ => PMF.pure 0) (fun _ => 0) = 1 := by
  simp [jointLaw]

example :
    jointLaw twoNodeDag 2 baseTwoNodeModule allFalseState = 1 := by
  simp [jointLaw, baseTwoNodeModule, allFalseState]

example : identityOneState 0 = 0 := by rfl

example : zeroOneState 0 = 0 := by rfl

example :
    jointLaw emptyDag 0 (fun v => Fin.elim0 v) (fun v => Fin.elim0 v) = 1 := by
  simp [jointLaw, emptyDag]

example :
    (Finset.univ : Finset (Fin 0)).prod (fun _ => (1 : ENNReal)) = 1 := by
  simp

end

end D5.S3.ConceptDynamics.Causal.SoftInterventionModularity
