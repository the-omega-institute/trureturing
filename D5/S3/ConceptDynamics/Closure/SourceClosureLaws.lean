/- GID: D5/S3/ConceptDynamics/Closure/SourceClosureLaws
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Closure/SourceClosureLaws
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A closure operator is extensive and monotone on source sets. -/

import Mathlib.Order.Closure

/- Library-search audit trail (2026-08-25):
   * `rg -n -F 'source_closure_extensive_and_monotone' D5 Golden/Frozen/accepted`
     found no repository theorem with the two source clauses.
   * The exact canonical Mathlib object is `ClosureOperator`; its public fields
     `le_closure` and `monotone` directly supply the displayed laws.
   * `rg -n 'def .*closure.*:=.*fun.*union|def .*cl.*\(.*Set' D5/S3`
     found no duplicate closure body; no sibling closure object is redeclared.
   * No separate stronger theorem was found in the pinned Mathlib search; this is
     an exact application of the canonical closure structure.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Closure.SourceClosureLaws

/-- Every canonical closure operator contains its input and preserves inclusion.
These are the two source closure laws, applied directly to Mathlib's object. -/
theorem source_closure_extensive_and_monotone
    {Carrier : Type*}
    (closure : ClosureOperator (Set Carrier))
    (S T : Set Carrier) :
    S ⊆ closure S ∧ (S ⊆ T → closure S ⊆ closure T) := by
  exact ⟨closure.le_closure S, fun hST => closure.monotone hST⟩

/-- The identity closure gives a concrete model of both public laws. -/
example (S T : Set Bool) (hST : S ⊆ T) :
    S ⊆ ClosureOperator.id (Set Bool) S ∧
      ClosureOperator.id (Set Bool) S ⊆ ClosureOperator.id (Set Bool) T := by
  have h := source_closure_extensive_and_monotone
    (ClosureOperator.id (Set Bool)) S T
  constructor
  · simpa only [ClosureOperator.id_apply] using h.1
  · simpa only [ClosureOperator.id_apply] using h.2 hST

#print axioms source_closure_extensive_and_monotone

end D5.S3.ConceptDynamics.Closure.SourceClosureLaws
