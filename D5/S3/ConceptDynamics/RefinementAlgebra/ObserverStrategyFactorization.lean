/- GID: D5/S3/ConceptDynamics/RefinementAlgebra/ObserverStrategyFactorization
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/RefinementAlgebra/ObserverStrategyFactorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Observer strategy implementation is equivalent to kernel containment. -/

import D5.S3.ConceptDynamics.ConceptJoinUniversal
import Mathlib.Data.Setoid.Basic

/- Library-search audit trail (2026-08-27):
   * Exact repository primitives `Concept` and `Refines` are imported and used
     directly. The frozen `effective_refines_iff_reverse_kernel` theorem requires
     both readouts to be effective, while the source imposes effectiveness only
     on the observer interface, so it is not an exact hit.
   * `AnswerabilityCriterion.answerability_criterion` uses an anchored target and
     does not publicly state kernel inclusion, so it is not an exact hit.
   * Pinned Mathlib's `Function.factorsThrough_iff` is adjacent but carries a
     `Nonempty` codomain assumption rather than the source interface-surjectivity
     premise. Exact hits `Function.surjInv` and `Function.rightInverse_surjInv`
     provide the section used to construct the factor.
   * Body-shape searches for a factorization iff reverse kernel inclusion with
     only the factoring-through interface surjective found no existing D5
     theorem. No new `def` or `abbrev` is introduced. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.RefinementAlgebra.ObserverStrategyFactorization

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal

universe u

/-- A policy is implementable from an effective interface exactly when it is
constant on every interface fiber. -/
theorem observer_strategy_factorization
    {X O Policy : Type u}
    (q : Concept X O) (policy : Concept X Policy)
    (q_surjective : Function.Surjective q) :
    Refines policy q ↔ Setoid.ker q ≤ Setoid.ker policy := by
  constructor
  · rintro ⟨factor, hfactor⟩ x y hxy
    calc
      policy x = factor (q x) := congrFun hfactor x
      _ = factor (q y) := congrArg factor hxy
      _ = policy y := (congrFun hfactor y).symm
  · intro hkernel
    let representative : O → X := Function.surjInv q_surjective
    have representativeRight : Function.RightInverse representative q :=
      Function.rightInverse_surjInv q_surjective
    refine ⟨fun observation => policy (representative observation), ?_⟩
    funext x
    change policy x = policy (representative (q x))
    exact hkernel (representativeRight (q x)).symm

example :
    Refines (fun x : Bool => decide x) (id : Concept Bool Bool) ↔
      Setoid.ker (id : Concept Bool Bool) ≤
        Setoid.ker (fun x : Bool => decide x) := by
  exact observer_strategy_factorization
    (id : Concept Bool Bool) (fun x : Bool => decide x) Function.surjective_id

#print axioms observer_strategy_factorization

end D5.S3.ConceptDynamics.RefinementAlgebra.ObserverStrategyFactorization
