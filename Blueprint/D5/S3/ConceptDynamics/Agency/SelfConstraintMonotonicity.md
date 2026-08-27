# Self-Constraint Monotonicity

## Abstract

Appending one ledger record can only shrink the actions consistent with every record.

**Theorem 1.1 (An appended record shrinks the consistent action set).**

$$\forall State \in Type, Record \in Type, Action \in Type, consistent \in State \to \left(Record \to \left(Action \to Prop\right)\right), x \in State, L \in \operatorname{List}\left(Record\right), q \in Record,\; \{a: Action \mid \forall r \in \operatorname{append}\left(L, \operatorname{singleton}\left(q\right)\right), \operatorname{consistent}\left(x, r, a\right)\} \subseteq \{a: Action \mid \forall r \in L, \operatorname{consistent}\left(x, r, a\right)\}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Agency/SelfConstraintMonotonicity.appended_record_shrinks_consistent_actions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A state-indexed relation says whether a candidate action is consistent with one ledger record. The old and new admissible action sets are constructed directly by requiring this relation for every record in the old ledger and in its one-record extension.

Every old record remains a member after the append. Therefore an action satisfying every constraint in the extended ledger satisfies every constraint in the old ledger.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Agency/SelfConstraintMonotonicity.appended_record_shrinks_consistent_actions`
