/- GID: D5/S3/ConceptDynamics/Audits/PartialTestsLeaveDefect
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Audits/PartialTestsLeaveDefect
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Partial tests can pass while a disjoint nonempty defect set remains. -/

import Mathlib.Data.Set.Insert

/- Library-search audit trail (2026-08-25):
   * Searches for passing tests, possible defects, and nonempty disjoint set
     countermodels found only the frozen predecessor, whose covered set is empty.
   * Pinned Mathlib supplies `Set.disjoint_left` and the singleton set lemmas used
     below, but no theorem packages the required shared countermodel.
   * A body-shape search for existential Boolean set pairs found no reusable D5
     primitive. This module introduces no definition or abbreviation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Audits.PartialTestsLeaveDefect

/-- A nonempty test family can pass because its covered candidates are disjoint
from the actual defects, while a defect still remains. All four clauses use the
same covered and defect sets. -/
theorem passing_partial_tests_can_leave_a_defect :
    ∃ covered defects : Set Bool,
      covered.Nonempty ∧
        defects.Nonempty ∧
        Disjoint covered defects ∧
        ∀ candidate, candidate ∈ covered → candidate ∉ defects := by
  refine ⟨{false}, {true}, ?_, ?_, ?_, ?_⟩
  · exact ⟨false, Set.mem_singleton false⟩
  · exact ⟨true, Set.mem_singleton true⟩
  · simp
  · intro candidate hCovered hDefect
    simp only [Set.mem_singleton_iff] at hCovered hDefect
    exact Bool.false_ne_true (hCovered.symm.trans hDefect)

#print axioms passing_partial_tests_can_leave_a_defect

end D5.S3.ConceptDynamics.Audits.PartialTestsLeaveDefect
