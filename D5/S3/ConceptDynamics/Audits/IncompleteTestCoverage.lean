/- GID: D5/S3/ConceptDynamics/Audits/IncompleteTestCoverage
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Audits/IncompleteTestCoverage
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Passing a strict partial coverage cannot establish an empty defect set. -/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Insert

/- Library-search audit trail (2026-08-25):
   * `rg -n -F 'incomplete_test_coverage' D5 Golden/Frozen/accepted` found no hit.
   * Searches for test coverage, strict partial sets, and defect elimination found
     no theorem packaging the source implication; the nearby `defectRelation`
     modules use a different target-sensitive carrier.
   * Pinned Mathlib's `Set.ssubset_iff_exists` and `Set.eq_empty_iff_forall_not_mem`
     are the exact set witnesses used below; no stronger theorem is available.
   * `rg -n 'def .*coverage.*\(.*ssubset|def .*defect.*Set' D5/S3/ConceptDynamics`
     found no body-shape duplicate before this theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Audits.IncompleteTestCoverage

/-- If a test family covers a strict subset of the possible defect set and every
covered candidate is ruled out by the passing tests, the full defect set is still
nonempty. Thus passing the partial test family cannot establish completeness. -/
theorem passed_partial_tests_leave_a_possible_defect
    {Candidate : Type*}
    (covered defects : Set Candidate)
    (coverageStrict : covered ⊂ defects)
    (allTestsPass : ∀ candidate, candidate ∈ covered → candidate ∉ defects) :
    covered = ∅ ∧ defects.Nonempty := by
  constructor
  · apply Set.eq_empty_iff_forall_notMem.mpr
    intro candidate hCovered
    exact allTestsPass candidate hCovered (coverageStrict.1 hCovered)
  · rcases (Set.ssubset_iff_exists.mp coverageStrict).2 with
      ⟨candidate, hDefect, _⟩
    exact ⟨candidate, hDefect⟩

/-- The strict-set and passing-test premises have a concrete two-candidate model. -/
example :
    let covered : Set Bool := ∅
    let defects : Set Bool := {true}
    covered ⊂ defects ∧
      (∀ candidate, candidate ∈ covered → candidate ∉ defects) ∧
      defects.Nonempty := by
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · exact (Set.ssubset_iff_of_subset (Set.empty_subset _)).2
      ⟨true, Set.mem_singleton true, fun h => h⟩
  · intro candidate hCovered
    exact False.elim (by simpa using hCovered)
  · exact ⟨true, Set.mem_singleton true⟩

#print axioms passed_partial_tests_leave_a_possible_defect

end D5.S3.ConceptDynamics.Audits.IncompleteTestCoverage
