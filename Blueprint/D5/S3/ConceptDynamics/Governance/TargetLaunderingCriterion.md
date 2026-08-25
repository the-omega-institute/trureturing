# Target Laundering Criterion

## Abstract

Target laundering combines freeze visibility, protected-coordinate change, same-round regrading, and attribution to the original commitment.

**Theorem 1.1 (The canonical definition regroups into three clauses).**

$$\begin{gathered}\forall evaluate, oldK, newK, Z, report,\\{}\operatorname{TargetLaundering}\left(evaluate, oldK, newK, Z, report\right) \iff\\{}\operatorname{FreezeVisibleProtectedChange}\left(oldK, newK, Z\right) \land\\{}\operatorname{RegradesOldRound}\left(evaluate, oldK, newK, Z, report\right) \land\\{}\operatorname{AttributesToOriginalCommitment}\left(evaluate, oldK, newK, Z, report\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Governance/TargetLaunderingCriterion.target_laundering_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The old and revised commitments share one round index. Event identifiers and times remain independent types, and every protected coordinate is projected directly from the revised commitment.

The regrade report is indexed by the actual evaluator. Its proof field certifies the reported verdict as the evaluator's value on the revised commitment and old evidence.

A separate temporal predicate compares a Time-valued arrival with the revised freeze time. The source supplies no bridge equating that comparison with freeze-event visibility.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Governance/TargetLaunderingCriterion.target_laundering_criterion`
