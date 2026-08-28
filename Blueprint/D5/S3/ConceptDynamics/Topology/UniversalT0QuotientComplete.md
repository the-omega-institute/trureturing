# Complete Universal T0 Quotient

## Abstract

The canonical separation quotient is T0 and has its unique continuous factorization.

**Theorem 1.1 (The separation quotient is T0 and universal).**

$$\forall X, Y: \operatorname{Type},\\{}[\operatorname{TopologicalSpace}(X)], [\operatorname{TopologicalSpace}(Y)], [\operatorname{T0Space}(Y)],\\{}f: X \to Y, \operatorname{Continuous}(f) \Rightarrow\\{}\operatorname{T0Space}(\operatorname{SeparationQuotient} X) \land \ \exists! barf: \operatorname{SeparationQuotient} X \to Y, \operatorname{Continuous}(barf) \land f = barf \circ \operatorname{mk}.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Topology/UniversalT0QuotientComplete.universal_t0_quotient_complete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source space and target space carry independent topologies, and the target is T0. The map f is an arbitrary continuous map between them.

The first public conclusion records the canonical T0 structure on the separation quotient. The second gives the unique continuous factor whose composite with the canonical projection is f.

The T0 structure is the pinned canonical Mathlib instance, while the factorization clause is supplied by the frozen family theorem.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Topology/UniversalT0QuotientComplete.universal_t0_quotient_complete`
- Dependency: [D5/S3/ConceptDynamics/Topology/UniversalT0Quotient](UniversalT0Quotient.md)
