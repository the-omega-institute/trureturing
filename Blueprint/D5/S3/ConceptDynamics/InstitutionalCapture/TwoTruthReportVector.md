# Two-Truth Report Vector

## Abstract

At the half-honest boundary, one report vector is admissible for both Boolean truths.

**Theorem 1.1 (One report vector supports two allowed truth worlds).**

$$\begin{aligned}\forall n, f \in \mathbb{N},\\n \leq 2 \times f \Rightarrow \exists H0, H1: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\\\operatorname{Disjoint}\left(H0, H1\right) \land \operatorname{card}\left(H0\right) = n - f \land \operatorname{card}\left(H1\right) = n - f \land\\\exists reports: \operatorname{Fin}\left(n\right) \to Bool, {\forall reporter \in H0, reports(reporter) = false} \land {\forall reporter \in H1, reports(reporter) = true} \land\\\operatorname{byzantineCount}\left(reports, false\right) \leq f \land \operatorname{byzantineCount}\left(reports, true\right) \leq f.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InstitutionalCapture/TwoTruthReportVector.two_truth_report_vector_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reports form a Boolean vector indexed by Fin n, and byzantineCount counts entries that disagree with a proposed common truth.

When n is at most f, the constant-false vector meets both bounds. Otherwise the vector is true on the first f indices and false elsewhere. Its two disagreement counts are f and n minus f, and the threshold bounds both by f. Subsets of the reporters agreeing with each truth give disjoint groups H0 and H1, each with exactly n minus f members.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InstitutionalCapture/TwoTruthReportVector.two_truth_report_vector_exists`
- Dependency: [D5/S3/ConceptDynamics/InstitutionalCapture/ByzantineMajorityRecovery](ByzantineMajorityRecovery.md)
