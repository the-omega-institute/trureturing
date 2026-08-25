# Incomplete Test Coverage

## Abstract

Passing a strict partial coverage cannot establish an empty defect set.

**Theorem 1.1 (Partial tests leave a possible defect).**

$$\forall Candidate: \operatorname{Type}, covered, defects: \operatorname{Set}\left(Candidate\right),\\{}\operatorname{ssubset}\left(covered, defects\right) \land \forall d \in Candidate,\; d \in covered \Rightarrow \neg d \in defects \Rightarrow\\{}covered = \emptyset \land \exists d \in Candidate,\; d \in defects.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Audits/IncompleteTestCoverage.passed_partial_tests_leave_a_possible_defect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The covered set and the full defect set are independent source predicates; strict inclusion records that the test family does not cover every possible defect.

The all-tests-pass premise says every covered candidate is excluded. The public conclusion exposes both that the covered candidates are empty after passing and that an uncovered defect remains.

The proof applies the pinned Set.ssubset_iff_exists and set-extensionality lemmas directly. No completeness certificate is assumed or hidden.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Audits/IncompleteTestCoverage.passed_partial_tests_leave_a_possible_defect`
