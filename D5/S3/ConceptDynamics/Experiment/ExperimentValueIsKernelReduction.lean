/- GID: D5/S3/ConceptDynamics/Experiment/ExperimentValueIsKernelReduction
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Experiment/ExperimentValueIsKernelReduction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Constant Fin-1000 is inert; one bit identifies Bool; degeneracies need no assumptions. -/

import D5.S3.ConceptDynamics.Experiment.ExperimentIdentifiability
import Mathlib.Data.Fintype.Card

/- Library-search audit trail (2026-08-24):
   * `rg -n -F 'experiment_value_is_kernel_reduction' D5
     Golden/Frozen/accepted` exited 1 with no declaration-name collision.
   * The five modules in `D5/S3/ConceptDynamics/Experiment` on `origin/dev` were
     inspected. `ExperimentExpansionMonotonicity` proves only general antitonicity;
     `ExperimentIdentifiability` characterizes target factorization; the other three
     concern capacity, infinite tomography, and multiple testing. None supplies both
     concrete witnesses below.
   * Repository searches for `ResidualPair`, `residual pair`, `kernel reduction`,
     `experimentGain`, and identifiability found `BlindKernelReductionMeasure` and
     `ResidualJoinLaw`. The former adds a numerical weight and the latter gives a
     retained-residual intersection law; neither compares a 1000-symbol constant
     experiment with a decisive Boolean experiment.
   * Pinned Mathlib searches found `List.TFAE.out` and the finite/set simplification
     machinery used below, but no theorem with these two experiments. The bridge to
     factorization reuses the imported public theorem `identifiable_tfae`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Experiment.ExperimentValueIsKernelReduction

open D5.S3.ConceptDynamics.Experiment.ExperimentIdentifiability
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

universe u v w z

/-- A target residual pair agrees under every allowed experiment but disagrees
under the target readout. -/
def ResidualPair {Experiment : Type u} {State : Type v} {Response : Type w}
    {Target : Type z} (allowed : Set Experiment)
    (run : Experiment -> State -> Response) (target : State -> Target)
    (x y : State) : Prop :=
  (forall experiment, experiment ∈ allowed -> run experiment x = run experiment y) ∧
    target x ≠ target y

/-- All target residual pairs left by an allowed experiment family. -/
def residualPairs {Experiment : Type u} {State : Type v} {Response : Type w}
    {Target : Type z} (allowed : Set Experiment)
    (run : Experiment -> State -> Response) (target : State -> Target) :
    Set (State × State) :=
  {pair | ResidualPair allowed run target pair.1 pair.2}

/-- A target is identifiable exactly when the experiment family leaves no target
residual pair. -/
def TargetIdentifiable {Experiment : Type u} {State : Type v} {Response : Type w}
    {Target : Type z} (allowed : Set Experiment)
    (run : Experiment -> State -> Response) (target : State -> Target) : Prop :=
  ¬Exists fun x => Exists fun y => ResidualPair allowed run target x y

/-- The no-residual-pair criterion is the existing joint-readout factorization
criterion, specialized to a set-indexed experiment family. -/
theorem targetIdentifiable_iff_factorization
    {Experiment : Type u} {State : Type v} {Response : Type w} {Target : Type z}
    [Nonempty State] (allowed : Set Experiment)
    (run : Experiment -> State -> Response) (target : State -> Target) :
    TargetIdentifiable allowed run target ↔
      Exists fun factor : (forall _ : allowed, Response) -> Target =>
        target = factor ∘ jointReadout (fun experiment : allowed => run experiment.1) := by
  have criterion :
      (Exists fun factor : (forall _ : allowed, Response) -> Target =>
          target = factor ∘ jointReadout (fun experiment : allowed => run experiment.1)) ↔
        forall x y,
          (forall experiment : allowed, run experiment.1 x = run experiment.1 y) ->
            target x = target y :=
    (identifiable_tfae (fun experiment : allowed => run experiment.1) target).out 0 2
  constructor
  · intro noResidual
    apply criterion.mpr
    intro x y sameResponses
    by_contra differentTargets
    apply noResidual
    refine ⟨x, y, ?_⟩
    refine ⟨?_, differentTargets⟩
    intro experiment experimentAllowed
    exact sameResponses ⟨experiment, experimentAllowed⟩
  · intro factorization
    rintro ⟨x, y, sameResponses, differentTargets⟩
    apply differentTargets
    apply criterion.mp factorization
    intro experiment
    exact sameResponses experiment.1 experiment.2

/-- A nominally large experiment whose 1000-symbol response space is unused. -/
def largeOutputExperiment : Bool -> Fin 1000 := fun _ => 0

/-- The decisive one-bit experiment on the Boolean state space. -/
def bitExperiment : Bool -> Bool := id

/-- The Boolean target that the concrete experiments seek to identify. -/
def booleanTarget : Bool -> Bool := id

/-- Experiment value is witnessed by reduction of the target residual kernel, not
by output-space size: the constant 1000-symbol experiment changes nothing, while
the Boolean experiment removes all remaining target residual pairs. -/
theorem experiment_value_is_kernel_reduction :
    (Fintype.card (Fin 1000) > Fintype.card Bool ∧
      residualPairs (∅ : Set Unit) (fun _ => largeOutputExperiment) booleanTarget =
        residualPairs (Set.univ : Set Unit) (fun _ => largeOutputExperiment)
          booleanTarget ∧
      (TargetIdentifiable (∅ : Set Unit) (fun _ => largeOutputExperiment)
          booleanTarget ↔
        TargetIdentifiable (Set.univ : Set Unit) (fun _ => largeOutputExperiment)
          booleanTarget)) ∧
    (Fintype.card Bool = 2 ∧
      residualPairs (∅ : Set Unit) (fun _ => bitExperiment) booleanTarget =
        {(false, true), (true, false)} ∧
      residualPairs (Set.univ : Set Unit) (fun _ => bitExperiment) booleanTarget = ∅ ∧
      ¬TargetIdentifiable (∅ : Set Unit) (fun _ => bitExperiment) booleanTarget ∧
      TargetIdentifiable (Set.univ : Set Unit) (fun _ => bitExperiment)
        booleanTarget) := by
  constructor
  · refine ⟨by simp [Fintype.card_fin, Fintype.card_bool], ?_, ?_⟩
    · ext pair
      simp [residualPairs, ResidualPair, largeOutputExperiment]
    · constructor
      · intro identifiable
        exact (identifiable ⟨false, true, by
          simp [ResidualPair, largeOutputExperiment, booleanTarget]⟩).elim
      · intro identifiable
        exact (identifiable ⟨false, true, by
          simp [ResidualPair, largeOutputExperiment, booleanTarget]⟩).elim
  · refine ⟨Fintype.card_bool, ?_, ?_, ?_, ?_⟩
    · ext ⟨x, y⟩
      cases x <;> cases y <;>
        simp [residualPairs, ResidualPair, bitExperiment, booleanTarget]
    · ext ⟨x, y⟩
      simp [residualPairs, ResidualPair, bitExperiment, booleanTarget]
    · intro identifiable
      exact identifiable ⟨false, true, by
        simp [ResidualPair, bitExperiment, booleanTarget]⟩
    · rintro ⟨x, y, sameResponses, differentTargets⟩
      exact differentTargets (sameResponses () (Set.mem_univ ()))

example :
    largeOutputExperiment false = largeOutputExperiment true ∧
      bitExperiment false ≠ bitExperiment true := by
  decide

#print axioms experiment_value_is_kernel_reduction

end D5.S3.ConceptDynamics.Experiment.ExperimentValueIsKernelReduction
