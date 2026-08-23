# Relational Precondition Adjunction

## Abstract

Relational strongest postconditions are adjoint to universal weakest preconditions.

**Theorem 1.1 (Relational adjunction and the may-must distinction).**

$$\begin{gathered}\forall X, Y: \operatorname{Type},\\{}R: \operatorname{SetRel}\left(X, Y\right), P: \operatorname{Set}\left(X\right), Q: \operatorname{Set}\left(Y\right),\\{}(\operatorname{relationalStrongestPostcondition}\left(R, P\right) \subseteq Q \iff P \subseteq \operatorname{universalWeakestPrecondition}\left(R, Q\right)) \land\\{}(false \in \operatorname{existentialPrecondition}\left(nondeterministicBooleanRelation, successfulOutcome\right) \land\\{}\neg (false \in \operatorname{universalWeakestPrecondition}\left(nondeterministicBooleanRelation, successfulOutcome\right))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Knowledge/RelationalPreconditionAdjunction.relational_adjunction_and_may_not_guarantee` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The relation is a set of source-target pairs. The relational strongest postcondition and existential precondition are respectively the pinned library's relational image and preimage. The universal weakest precondition contains states whose every related outcome is in the target.

The first displayed conjunct states both directions of the relational adjunction for arbitrary source and target predicates.

The remaining public conjuncts use a Boolean relation that allows both outcomes from false and the singleton successful outcome true. A successful path exists, while the false outcome refutes a universal success guarantee.

## References

- Truth anchor: `D5/S3/ObserverMemory/Knowledge/RelationalPreconditionAdjunction.relational_adjunction_and_may_not_guarantee`
- Dependency: [D5/S3/ObserverMemory/Knowledge/StrongestPostconditionAdjunction](StrongestPostconditionAdjunction.md)
