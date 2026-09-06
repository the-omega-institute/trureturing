# Concept Fiber Decomposition

## Abstract

Every concept readout decomposes its source into dependent fibers.

**Definition 1.1 (A concept is a typed readout).**

$$\forall X, B: \operatorname{Type}, \operatorname{Concept}\left(X, B\right) = X \to B.$$

*Formalization.* `D5/S3/ConceptDynamics/ConceptFiberDecomposition.Concept` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For arbitrary source and coordinate types X and B, a concept from X to B is exactly a function assigning one B-coordinate to each X-object.

**Theorem 1.2 (Concept fiber decomposition).**

$$\forall X, B_{C}: \operatorname{Type}, q_{C}: X \to B_{C},\ \operatorname{Nonempty}(X \equiv \sum _{b: B_{C}} R_{C}(b)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ConceptFiberDecomposition.concept_fiber_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A concept is a readout q_C : X -> B_C. Its residual fiber over b is the dependent pair of x : X with a path q_C x = b.

Mathlib's sigmaFiberEquiv supplies the explicit forward map sending x to q_C x with its canonical fiber witness and the backward map forgetting the coordinate. psigmaEquivSubtype and sigmaCongrRight transport that equivalence to the proof-relevant residual fiber notation used here.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ConceptFiberDecomposition.Concept`
- Truth anchor: `D5/S3/ConceptDynamics/ConceptFiberDecomposition.concept_fiber_decomposition`
