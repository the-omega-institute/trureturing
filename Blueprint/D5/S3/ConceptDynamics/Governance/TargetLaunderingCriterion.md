# Target Laundering Criterion

## Abstract

Target laundering combines post-arrival protected-coordinate change, same-round regrading, and attribution to the original commitment.

**Theorem 1.1 (The boxed temporal definition regroups into three clauses).**

$$\begin{gathered}\forall arrival, evaluate, oldK, newK, Z, report,\\{}\operatorname{TargetLaundering}\left(arrival, evaluate, oldK, newK, Z, report\right) \iff\\{}\operatorname{PostArrivalProtectedChange}\left(arrival, oldK, newK, Z\right) \land\\{}\operatorname{RegradesOldRound}\left(evaluate, oldK, newK, Z, report\right) \land\\{}\operatorname{AttributesToOriginalCommitment}\left(evaluate, oldK, newK, Z, report\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Governance/TargetLaunderingCriterion.target_laundering_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The old and revised commitments share one round index. Event identifiers and times remain independent types, and every protected coordinate is projected directly from the revised commitment.

The regrade report is indexed by the actual evaluator. Its proof field certifies the reported verdict as the evaluator's value on the revised commitment and old evidence. Its timestamp remains data, not an extra premise of the boxed criterion.

DECT 50.4 defines this clause by a strict comparison between the Time-valued first arrival and the revised freeze time. The later Lean sketch instead uses visibility at the freeze EventId.

Those source formulations are not equivalent under the stated data: a record first seen exactly at the freeze event is visible there but does not arrive strictly before it. The Lean module retains the sketch separately; an exact bridge reconciles only the two arrival tests, while the sketch-only timestamp stays explicit.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Governance/TargetLaunderingCriterion.target_laundering_criterion`
