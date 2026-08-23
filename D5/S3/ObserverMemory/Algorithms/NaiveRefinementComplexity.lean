/- GID: D5/S3/ObserverMemory/Algorithms/NaiveRefinementComplexity
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/NaiveRefinementComplexity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite signature refinement has linear rounds and the stated sorting and hashing costs. -/

import D5.S3.ObserverMemory.Algorithms.ControlledFiniteStability
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/- Library-search audit trail (2026-08-21):
   * Repository exact hit `controlled_finite_stability` is imported and applied
     to the singleton-input specialization of the deterministic successor.
   * Repository exact hits `controlledStabilityDepth`, `controlledSignature`,
     and `controlledDepthRelation` supply the canonical stopping test and the
     recursive signature semantics rather than a new family-local copy.
   * Pinned Mathlib exact hits `Asymptotics.IsBigO.mul`,
     `Asymptotics.IsBigO.of_bound`, and `Asymptotics.isBigO_refl` are applied
     to compose the primitive per-round and per-state cost estimates.
   * Loogle and LeanSearch executables were unavailable. Repository and pinned
     Mathlib searches found no single theorem packaging all four complexity
     clauses. -/

namespace D5.S3.ObserverMemory.Algorithms.NaiveRefinementComplexity

open D5.S3.ObserverMemory.Algorithms.ControlledFiniteStability
open Filter

universe u v

noncomputable section

/-- The source algorithm's stopping round, obtained by refining the recursive
signature for the deterministic successor viewed as a singleton input. -/
def refinementRounds {ι : Type u} {Y O : ι -> Type v}
    (tau : forall i, Y i -> Y i) (readout : forall i, Y i -> O i) : ι -> Nat :=
  fun i => controlledStabilityDepth (fun _ : PUnit => tau i) (readout i)

/-- Sorting work accumulated over the initial labeling and every strict
refinement round. -/
def sortingRefinementWork {ι : Type u}
    (rounds : ι -> Nat) (sortingRoundWork : ι -> Real) : ι -> Real :=
  fun i => ((rounds i + 1 : Nat) : Real) * sortingRoundWork i

/-- Expected hashing work accumulated over the initial labeling and every
strict refinement round. -/
def expectedHashRefinementWork {ι : Type u}
    (rounds : ι -> Nat) (expectedHashRoundWork : ι -> Real) : ι -> Real :=
  fun i => ((rounds i + 1 : Nat) : Real) * expectedHashRoundWork i

/-- Extra workspace for one fixed-size record per state. -/
def refinementWorkspace {ι : Type u}
    (stateCount : ι -> Nat) (workspacePerState : ι -> Real) : ι -> Real :=
  fun i => (stateCount i : Real) * workspacePerState i

/-- For finite deterministic systems with realized readouts, canonical
signature refinement takes at most the difference between the state and
readout counts. Consequently, a sorting implementation with one-round cost
linearithmic in the state count has the displayed total cost, its record
workspace is linear, and constant-expected-time hashing removes the logarithm.

The cost functions in the hypotheses describe only one relabeling round or
one state record. The three concluded costs are constructed above by composing
those primitives with the canonical source stopping round. -/
theorem naive_refinement_complexity
    {ι : Type u} {Y O : ι -> Type v}
    [forall i, Fintype (Y i)] [forall i, Fintype (O i)]
    [forall i, Nonempty (Y i)] [forall i, Nonempty (O i)]
    (l : Filter ι)
    (tau : forall i, Y i -> Y i) (readout : forall i, Y i -> O i)
    (readoutSurjective : forall i, Function.Surjective (readout i))
    (sortingRoundWork expectedHashRoundWork workspacePerState : ι -> Real)
    (sortingRoundBound : sortingRoundWork =O[l] (fun i =>
      (Fintype.card (Y i) : Real) * Real.log (Fintype.card (Y i) : Real)))
    (expectedHashRoundBound : expectedHashRoundWork =O[l] (fun i =>
      (Fintype.card (Y i) : Real)))
    (workspacePerStateBound : workspacePerState =O[l] (fun _ => (1 : Real))) :
    (forall i,
      refinementRounds tau readout i <=
        Fintype.card (Y i) - Fintype.card (O i)) /\
    sortingRefinementWork (refinementRounds tau readout) sortingRoundWork
        =O[l] (fun i =>
      (Fintype.card (Y i) : Real) *
        ((Fintype.card (Y i) - Fintype.card (O i) + 1 : Nat) : Real) *
          Real.log (Fintype.card (Y i) : Real)) /\
    refinementWorkspace (fun i => Fintype.card (Y i)) workspacePerState
        =O[l] (fun i => (Fintype.card (Y i) : Real)) /\
    expectedHashRefinementWork
        (refinementRounds tau readout) expectedHashRoundWork
        =O[l] (fun i =>
      (Fintype.card (Y i) : Real) *
        ((Fintype.card (Y i) - Fintype.card (O i) + 1 : Nat) : Real)) := by
  have roundBound : forall i,
      refinementRounds tau readout i <=
        Fintype.card (Y i) - Fintype.card (O i) := by
    intro i
    have finiteStability := controlled_finite_stability
      (fun _ : PUnit => tau i) (readout i) (readoutSurjective i)
    exact finiteStability.2.2.2.2.1.trans finiteStability.2.2.2.2.2
  have roundFactorBound :
      (fun i => ((refinementRounds tau readout i + 1 : Nat) : Real))
          =O[l] fun i =>
        ((Fintype.card (Y i) - Fintype.card (O i) + 1 : Nat) : Real) := by
    apply Asymptotics.IsBigO.of_bound 1
    exact Filter.Eventually.of_forall fun i => by
      have h := Nat.add_le_add_right (roundBound i) 1
      rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast h
  have sortingTotalBound := roundFactorBound.mul sortingRoundBound
  have workspaceTotalBound :=
    (Asymptotics.isBigO_refl
      (fun i => (Fintype.card (Y i) : Real)) l).mul workspacePerStateBound
  have expectedHashTotalBound := roundFactorBound.mul expectedHashRoundBound
  refine ⟨roundBound, ?_, ?_, ?_⟩
  · refine sortingTotalBound.congr (fun i => ?_) (fun i => ?_)
    · rfl
    · ring
  · refine workspaceTotalBound.congr (fun i => ?_) (fun i => ?_)
    · rfl
    · ring
  · refine expectedHashTotalBound.congr (fun i => ?_) (fun i => ?_)
    · rfl
    · ring

/-- All carrier and primitive cost hypotheses have a concrete simultaneous
model: the one-state identity system with zero implementation cost. -/
example :
    let _tau : Unit -> Unit -> Unit := fun _ => id
    let readout : Unit -> Unit -> Unit := fun _ => id
    let zeroCost : Unit -> Real := fun _ => 0
    (forall i, Function.Surjective (readout i)) /\
      (zeroCost =O[(⊤ : Filter Unit)] fun _ =>
        (Fintype.card Unit : Real) * Real.log (Fintype.card Unit : Real)) /\
      (zeroCost =O[(⊤ : Filter Unit)] fun _ => (Fintype.card Unit : Real)) /\
      (zeroCost =O[(⊤ : Filter Unit)] fun _ => (1 : Real)) := by
  dsimp
  exact ⟨fun _ => Function.surjective_id,
    Asymptotics.isBigO_zero _ _, Asymptotics.isBigO_zero _ _,
    Asymptotics.isBigO_zero _ _⟩

#print axioms naive_refinement_complexity

end

end D5.S3.ObserverMemory.Algorithms.NaiveRefinementComplexity
