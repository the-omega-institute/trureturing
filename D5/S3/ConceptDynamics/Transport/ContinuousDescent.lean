/- GID: D5/S3/ConceptDynamics/Transport/ContinuousDescent
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Transport/ContinuousDescent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A continuous fiber-constant map descends uniquely through a quotient map. -/

import Mathlib.Topology.ContinuousMap.Basic

/- Library-search audit trail (2026-08-21):
   * `rg -n -i 'continuous.*(descent|descend|lift|factor)|quotient.*continuous|
     IsQuotientMap|QuotientMap' D5 -g '*.lean'` found the adjacent set-level theorem
     `DynamicsDescent.dynamics_descends_iff`, but no continuous existence-and-uniqueness result.
   * The corresponding searches in pinned Mathlib found the exact reusable declarations
     `Topology.IsQuotientMap.lift`, `Topology.IsQuotientMap.lift_comp`, and
     `ContinuousMap.cancel_right`. The proof below is the thinnest wrapper around them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ConceptDynamics.Transport.ContinuousDescent

/-- A continuous map constant on the fibers of a quotient map has a unique continuous descent. -/
theorem continuous_descent
    {X B Y : Type*} [TopologicalSpace X] [TopologicalSpace B] [TopologicalSpace Y]
    (q : C(X, B)) (T : C(X, Y))
    (hq : Topology.IsQuotientMap q) (hT : Function.FactorsThrough T q) :
    ∃! descended : C(B, Y), T = descended.comp q := by
  refine ⟨hq.lift T hT, (hq.lift_comp T hT).symm, ?_⟩
  intro candidate hCandidate
  apply (ContinuousMap.cancel_right hq.surjective).mp
  exact hCandidate.symm.trans (hq.lift_comp T hT).symm

/-- The identity quotient on `Bool` witnesses simultaneous satisfiability of the hypotheses. -/
example :
    ∃! descended : C(Bool, Bool),
      ContinuousMap.id Bool = descended.comp (ContinuousMap.id Bool) := by
  apply continuous_descent (q := ContinuousMap.id Bool) (T := ContinuousMap.id Bool)
  · exact Topology.IsQuotientMap.id
  · intro _ _ h
    exact h

example : Bool := false

#print axioms continuous_descent

end D5.S3.ConceptDynamics.Transport.ContinuousDescent
