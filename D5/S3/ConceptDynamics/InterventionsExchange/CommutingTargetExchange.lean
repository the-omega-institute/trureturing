/- GID: D5/S3/ConceptDynamics/InterventionsExchange/CommutingTargetExchange
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InterventionsExchange/CommutingTargetExchange
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Commuting state interventions have an empty target-level order-defect set. -/

import D5.S3.ConceptDynamics.ConceptFiberDecomposition
import Mathlib.Data.Set.Lattice

/- Library-search audit trail (2026-08-25):
   * `rg -n -F '({x | target' D5/S3/ConceptDynamics --glob '*.lean'` found
     only the translation-specific theorem `abelian_translation_commutation_and_defect_exclusion`;
     it does not state the general commuting-map defect conclusion.
   * `rg -n -F 'Function.Commute' D5/S3/ConceptDynamics --glob '*.lean'` found
     completion and translation results, but no empty target-defect theorem.
   * The exact canonical source carrier hit is `Concept` in
     `ConceptFiberDecomposition`; it is imported rather than redeclared.
   * Pinned Mathlib supplies `Set.eq_empty_iff_forall_notMem` and function
     congruence, which are applied directly below. `loogle` and `leansearch`
     were absent from PATH.
   * Body-shape check before introducing `commutationDefect`:
     `rg -n -F '({x | target' D5/S3/ConceptDynamics --glob '*.lean'` hit only
     the translation-specific source shape above; no canonical general defect
     primitive exists, so this source-semantic definition is imported nowhere.
 -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InterventionsExchange.CommutingTargetExchange

open D5.S3.ConceptDynamics.ConceptFiberDecomposition

/- The source's Comm object: states whose target values depend on intervention order. -/
def commutationDefect {X Target : Type*}
    (first second : X → X) (target : Concept X Target) : Set X :=
  {x | target ((first ∘ second) x) ≠ target ((second ∘ first) x)}

/- If the state maps commute, every target is constant on the two compositions. -/
theorem commuting_target_defect_empty
    {X Target : Type*} (first second : X → X)
    (hcomm : first ∘ second = second ∘ first)
    (target : Concept X Target) :
    commutationDefect first second target = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact hx (congrArg target (congrFun hcomm x))

example :
    commutationDefect (id : Bool → Bool) id (id : Concept Bool Bool) = ∅ := by
  exact commuting_target_defect_empty id id rfl id

#print axioms commuting_target_defect_empty

end D5.S3.ConceptDynamics.InterventionsExchange.CommutingTargetExchange
