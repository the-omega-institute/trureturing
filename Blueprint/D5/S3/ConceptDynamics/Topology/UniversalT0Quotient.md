# Universal T0 Quotient

## Abstract

The separation quotient has the universal property for continuous maps to T0 spaces.

**Theorem 1.1 (Universal property of the T0 quotient).**

$$\forall X, Y: \operatorname{Type}, [\operatorname{TopologicalSpace}(X)], [\operatorname{TopologicalSpace}(Y)], [\operatorname{T0Space}(Y)], f: X \to Y, \operatorname{Continuous}(f) \Rightarrow \ \exists! barf: \operatorname{SeparationQuotient} X \to Y, \operatorname{Continuous}(barf) \land f = barf \circ \operatorname{mk}.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Topology/UniversalT0Quotient.universal_t0_quotient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a topological space X, the canonical separation quotient is a T0 space and its projection q identifies precisely inseparable points.

For every continuous map f from X to a T0 space Y, there is a unique continuous map from the separation quotient to Y whose composite with q is f. The proof uses Mathlib's separation-quotient lift, continuity theorem, and surjectivity of q.

Pinned Mathlib searches found the exact declarations SeparationQuotient.lift, SeparationQuotient.continuous_lift, SeparationQuotient.lift_comp_mk, Inseparable.map, Inseparable.eq, and Function.Surjective.injective_comp_right; no repository theorem with this combined universal property was found.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Topology/UniversalT0Quotient.universal_t0_quotient`
