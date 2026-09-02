# Revision Conflict Noncommutation

## Abstract

Reset-on-conflict revision is order-dependent on a concrete three-world model.

**Theorem 1.1 (Reset-on-conflict revision need not commute).**

$$A = \left\{0\right\}, P = \left\{1, 2\right\}, Q = \left\{0, 1\right\}\ \Rightarrow \operatorname{Rev}\left(Q, \operatorname{Rev}\left(P, A\right)\right) = \left\{1\right\} \land \operatorname{Rev}\left(P, \operatorname{Rev}\left(Q, A\right)\right) = \left\{1, 2\right\} \land \operatorname{Rev}\left(Q, \operatorname{Rev}\left(P, A\right)\right) \neq \operatorname{Rev}\left(P, \operatorname{Rev}\left(Q, A\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Revision/RevisionConflictNoncommutation.revision_conflict_noncommutation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let revision intersect the current admissible worlds with compatible evidence and reset to the evidence set after a total conflict. On the three-world carrier, take A = {0}, P = {1, 2}, and Q = {0, 1}.

Revising first by P and then by Q yields {1}; reversing the order yields {1, 2}. The two update paths are therefore unequal.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Revision/RevisionConflictNoncommutation.revision_conflict_noncommutation`
