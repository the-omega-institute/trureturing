/- GID: D5/S3/Observer/AgencySelf/AgencyEnrichment
   generality: G
   mirror-B: D5/B/S3/Observer/AgencySelf/AgencyEnrichment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Agency enrichment pairs current state and strategy, isolates the strategy residual inside current fibers, and becomes agency completion only after controlled behavior closure. -/

import D5.S3.ObserverMemory.Refinement.EffectiveImageKernelCriterion
import D5.S3.ObserverMemory.Refinement.JointReadoutSupremum
import D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality

/- Library-search audit trail (2026-08-29):
   * The repository `pairReadout` owner supplies the joint interface and its
     supremum law; `ControlledCompletion` supplies the actual dynamical closure.
   * The effective-image kernel criterion supplies the unique realized factor.
   * No parallel agency kernel or completion primitive is introduced here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.AgencySelf.AgencyEnrichment

open D5.S3.ObserverMemory.Refinement.EffectiveImageKernelCriterion
open D5.S3.ObserverMemory.Refinement.JointReadoutSupremum
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality

universe u v w z

/-- The interface-level enrichment that records current state and strategy. -/
abbrev agencyEnrichment
    {H : Type u} {B : Type v} {P : Type w}
    (current : H -> B) (strategy : H -> P) : H -> B × P :=
  pairReadout current strategy

/-- The pairs in one current-state fiber that remain separated by strategy. -/
def StrategyResidual
    {H : Type u} {B : Type v} {P : Type w}
    (current : H -> B) (strategy : H -> P) (x y : H) : Prop :=
  current x = current y ∧ strategy x ≠ strategy y

/-- Inside a current-state fiber, a pair either agrees under the enriched
readout or is a strategy residual. -/
theorem current_kernel_strategy_residual_partition
    {H : Type u} {B : Type v} {P : Type w}
    (current : H -> B) (strategy : H -> P) (x y : H) :
    current x = current y <->
      agencyEnrichment current strategy x =
          agencyEnrichment current strategy y ∨
        StrategyResidual current strategy x y := by
  constructor
  · intro sameCurrent
    by_cases sameStrategy : strategy x = strategy y
    · exact Or.inl (Prod.ext sameCurrent sameStrategy)
    · exact Or.inr ⟨sameCurrent, sameStrategy⟩
  · intro alternative
    rcases alternative with samePair | residual
    · exact congrArg Prod.fst samePair
    · exact residual.1

/-- The enriched kernel and the strategy residual are disjoint. -/
theorem agency_kernel_disjoint_strategy_residual
    {H : Type u} {B : Type v} {P : Type w}
    (current : H -> B) (strategy : H -> P) (x y : H) :
    ¬ (agencyEnrichment current strategy x =
          agencyEnrichment current strategy y ∧
        StrategyResidual current strategy x y) := by
  rintro ⟨samePair, residual⟩
  exact residual.2 (congrArg Prod.snd samePair)

/-- There is no strategy residual exactly when strategy is constant on every
current-state fiber. -/
theorem no_strategy_residual_iff_kernel_inclusion
    {H : Type u} {B : Type v} {P : Type w}
    (current : H -> B) (strategy : H -> P) :
    (forall x y, ¬ StrategyResidual current strategy x y) <->
      forall x y, current x = current y -> strategy x = strategy y := by
  constructor
  · intro noResidual x y sameCurrent
    by_contra differentStrategy
    exact noResidual x y ⟨sameCurrent, differentStrategy⟩
  · intro strategyOnFibers x y residual
    exact residual.2 (strategyOnFibers x y residual.1)

/-- Vanishing strategy residual is equivalent to a unique factor from the
realized current-state image to the realized strategy image. -/
theorem strategy_factorization_iff_no_residual
    {H : Type u} {B : Type v} {P : Type w}
    (current : H -> B) (strategy : H -> P) :
    (∃! factor : Set.range current -> Set.range strategy,
        forall x,
          factor (Set.rangeFactorization current x) =
            Set.rangeFactorization strategy x) <->
      forall x y, ¬ StrategyResidual current strategy x y := by
  constructor
  · intro factorization
    apply (no_strategy_residual_iff_kernel_inclusion current strategy).2
    exact
      (refinement_iff_kernel_inclusion_on_effective_images
        strategy current).1 factorization
  · intro noResidual
    apply
      (refinement_iff_kernel_inclusion_on_effective_images
        strategy current).2
    exact (no_strategy_residual_iff_kernel_inclusion current strategy).1 noResidual

/-- Pairing strategy adds no new distinction exactly when the strategy residual
vanishes. -/
theorem agency_enrichment_kernel_eq_current_iff_no_residual
    {H : Type u} {B : Type v} {P : Type w}
    (current : H -> B) (strategy : H -> P) :
    Setoid.ker (agencyEnrichment current strategy) = Setoid.ker current <->
      forall x y, ¬ StrategyResidual current strategy x y := by
  constructor
  · intro sameKernel
    apply (no_strategy_residual_iff_kernel_inclusion current strategy).2
    intro x y sameCurrent
    have sameEnriched :
        Setoid.ker (agencyEnrichment current strategy) x y := by
      rw [sameKernel]
      exact sameCurrent
    exact congrArg Prod.snd sameEnriched
  · intro noResidual
    have strategyOnFibers :=
      (no_strategy_residual_iff_kernel_inclusion current strategy).1 noResidual
    apply le_antisymm
    · intro x y sameEnriched
      exact congrArg Prod.fst sameEnriched
    · intro x y sameCurrent
      exact Prod.ext sameCurrent (strategyOnFibers x y sameCurrent)

/-- After a controlled action is specified, agency completion is the existing
complete controlled behavior of the enriched readout. -/
abbrev ControlledAgencyCompletion
    {U : Type z} {H : Type u} {B : Type v} {P : Type w}
    (update : U -> H -> H) (current : H -> B) (strategy : H -> P) :=
  ControlledCompletion update (agencyEnrichment current strategy)

/-- A visible Boolean state with a constant strategy has no strategy residual. -/
example :
    forall x y, ¬ StrategyResidual (fun x : Bool => x)
      (fun _ : Bool => PUnit.unit) x y := by
  intro x y residual
  exact residual.2 rfl

#print axioms current_kernel_strategy_residual_partition
#print axioms agency_kernel_disjoint_strategy_residual
#print axioms no_strategy_residual_iff_kernel_inclusion
#print axioms strategy_factorization_iff_no_residual
#print axioms agency_enrichment_kernel_eq_current_iff_no_residual

end D5.S3.Observer.AgencySelf.AgencyEnrichment
