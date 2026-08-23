# Concept Fiber Decomposition

## Abstract

Every concept readout decomposes its source into dependent fibers.

**Theorem 1.1 (Concept fiber decomposition).**

$$\forall X, B_{C}: \operatorname{Type}, q_{C}: X \to B_{C},\ \operatorname{Nonempty}(X \equiv \sum _{b: B_{C}} R_{C}(b)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ConceptFiberDecomposition.concept_fiber_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A concept is a readout q_C : X -> B_C. Its residual fiber over b is the dependent pair of x : X with a path q_C x = b.

Mathlib's sigmaFiberEquiv supplies the explicit forward map sending x to q_C x with its canonical fiber witness and the backward map forgetting the coordinate. psigmaEquivSubtype and sigmaCongrRight transport that equivalence to the proof-relevant residual fiber notation used here.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ConceptFiberDecomposition.concept_fiber_decomposition`
