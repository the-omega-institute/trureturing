/- GID: D5/S3/ConceptDynamics/Transport/CompactHausdorffDescent
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Transport/CompactHausdorffDescent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Compact-to-Hausdorff surjections are closed, quotient, and support descent. -/

import D5.S3.ConceptDynamics.Transport.ContinuousDescent
import Mathlib.Topology.Separation.Hausdorff

/- Library-search audit trail (2026-08-24):
   * Exact current-tree hit `ContinuousDescent.continuous_descent` supplies
     unique continuous factorization through any quotient map.
   * Exact pinned-Mathlib hits `Continuous.isClosedMap` and
     `Topology.IsQuotientMap.of_surjective_continuous` supply closedness and
     quotientness for a continuous surjection from compact to Hausdorff.
   * Repository searches for the combined compact-Hausdorff statement found
     no complete declaration. `loogle` and `leansearch` were unavailable. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Transport.CompactHausdorffDescent

open D5.S3.ConceptDynamics.Transport.ContinuousDescent

/-- A continuous surjection from compact to Hausdorff is closed and quotient;
every continuous fiber-constant map therefore has a unique continuous descent. -/
theorem compact_hausdorff_automatic_quotient
    {X B Y : Type*} [TopologicalSpace X] [TopologicalSpace B]
    [TopologicalSpace Y] [CompactSpace X] [T2Space B]
    (q : C(X, B)) (surjective : Function.Surjective q)
    (T : C(X, Y)) (fiber_constant : Function.FactorsThrough T q) :
    IsClosedMap q ∧
      Topology.IsQuotientMap q ∧
      ∃! factor : C(B, Y), T = factor.comp q := by
  have closed : IsClosedMap q := q.continuous.isClosedMap
  have quotient : Topology.IsQuotientMap q :=
    closed.isQuotientMap q.continuous surjective
  exact ⟨closed, quotient, continuous_descent q T quotient fiber_constant⟩

/- The identity map on a finite discrete space witnesses all public hypotheses. -/
example :
    IsClosedMap (ContinuousMap.id Bool) ∧
      Topology.IsQuotientMap (ContinuousMap.id Bool) ∧
      ∃! factor : C(Bool, Bool),
        ContinuousMap.id Bool = factor.comp (ContinuousMap.id Bool) := by
  apply compact_hausdorff_automatic_quotient
    (q := ContinuousMap.id Bool) (T := ContinuousMap.id Bool)
  · exact Function.surjective_id
  · intro _ _ h
    exact h

example : Bool := false

#print axioms compact_hausdorff_automatic_quotient

end D5.S3.ConceptDynamics.Transport.CompactHausdorffDescent
