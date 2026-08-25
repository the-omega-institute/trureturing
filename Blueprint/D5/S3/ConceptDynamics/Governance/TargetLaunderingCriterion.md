# Target Laundering Criterion

## Abstract

Target laundering combines post-arrival protected-coordinate change, an actual re-evaluation, and attribution to the original commitment.

**Theorem 1.1 (Target laundering has three necessary and sufficient clauses).**

$$\begin{gathered}\forall evaluate, filtration, original, revised, evidence,\\{}\forall report: \operatorname{RegradeReport}\left(evaluate\right),\\{}\operatorname{TargetLaundering}\left(evaluate, filtration, original, revised, evidence, report\right) \iff\\{}\operatorname{PostArrivalProtectedChange}\left(filtration, original, revised, evidence\right) \land\\{}\operatorname{RegradesOldRound}\left(original, revised, evidence, \operatorname{Time}\left(revised\right), report\right) \land\\{}\operatorname{AttributesToOriginalCommitment}\left(evaluate, original, revised, evidence, report\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Governance/TargetLaunderingCriterion.target_laundering_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The protected projection retains target chain, domain, tolerance, conditions, comparator, baseline, and weight specification. A common access filtration records that the evidence arrived before the revised commitment event.

The regrade report carries a verdict together with an equality to the actual evaluation of the revised commitment on the old evidence. The attribution clause therefore cannot be discharged by an arbitrary truth label.

A finite positive control changes a protected condition while retaining the same verdict, so unequal scores are not required. Separate false-side controls make each of the three clauses fail in isolation.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Governance/TargetLaunderingCriterion.target_laundering_criterion`
