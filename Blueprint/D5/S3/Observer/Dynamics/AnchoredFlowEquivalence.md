# Anchored Flow Equivalence

## Abstract

Anchored flow identity is characterized by enriched topological conjugacy.

**Theorem 1.1 (Anchored flow identity is enriched conjugacy).**

$$B \in \operatorname{observerIdentity}(A) \iff (\exists h: \operatorname{Homeomorph}(X, Y),\ h(A.anchor) = B.anchor \land\\(\forall t, x, h(A.dynamics(t)(x)) = B.dynamics(t)(h(x))) \land\\B.readout \circ h = A.readout \land\\(\forall t, x, B.cocycle(t)(h(x)) = A.cocycle(t)(x)) \land\\B.ledger \circ h = A.ledger) \land\\(\forall g: \operatorname{Homeomorph}(X, X),\ (g(A.anchor) = A.anchor \land (\forall t, x, g(A.dynamics(t)(x)) = A.dynamics(t)(g(x))) \land\\A.readout \circ g = A.readout \land (\forall t, x, A.cocycle(t)(g(x)) = A.cocycle(t)(x)) \land A.ledger \circ g = A.ledger) \Rightarrow g(A.anchor) = A.anchor).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Dynamics/AnchoredFlowEquivalence.anchored_flow_equivalence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A and B be compact connected Hausdorff carriers with continuous real flows, internally selected anchors, readouts, additive memory cocycles, and ledgers. Their primitive equivalence is constructed from a continuous bijection preserving each field.

B belongs to the observer identity class of A exactly when a homeomorphism sends anchor to anchor, conjugates every time slice, preserves readout by composition, and transports both cocycle and ledger data. Every enriched anchored self-conjugacy fixes the internally selected anchor, so it lies in the anchor's stabilizer.

Pinned Mathlib and Loogle returned isHomeomorph_iff_continuous_bijective as the exact bridge from the semantic continuous bijection to a homeomorphism. The Lean proof imports and applies that result directly.

## References

- Truth anchor: `D5/S3/Observer/Dynamics/AnchoredFlowEquivalence.anchored_flow_equivalence`
