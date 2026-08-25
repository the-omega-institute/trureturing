# Execution-Privacy Obstruction

## Abstract

A nonpublic target-sensitive core obstructs exact execution without new leakage.

**Theorem 1.1 (Execution and zero new leakage are incompatible).**

$$\forall X \in \operatorname{Type}, P \in \operatorname{Type}, L \in \operatorname{Type}, S \in \operatorname{Type}, E \in \operatorname{Type}, K \in \operatorname{Type}, Before \in \operatorname{Type}, After \in \operatorname{Type}, p \in X \to P, l \in X \to L, s \in X \to S, e \in X \to E, k \in X \to K, before \in X \to Before, after \in X \to After,\; \left(\operatorname{IsConceptMeet}(e, s, k) \land \left(\neg \operatorname{Refines}(k, before)\right)\right) \Rightarrow \left(\neg \left(\operatorname{Refines}(e, \operatorname{conceptJoin}(p, l)) \land \operatorname{StructurallyNoNewLeak}(p, l, s, before, after)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Disclosure/ExecutionPrivacyObstruction.execution_privacy_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The forced part is explicitly the meet of the target and sensitive readouts, while the prior leak is the before component named by the canonical structural no-new-leak predicate.

Exact realization and structural no-new-leak would force the sensitive part below the prior leak, contradicting the displayed obstruction premise.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Disclosure/ExecutionPrivacyObstruction.execution_privacy_obstruction`
- Dependency: [D5/S3/ConceptDynamics/Disclosure/ExactTargetForcedLeak](ExactTargetForcedLeak.md)
