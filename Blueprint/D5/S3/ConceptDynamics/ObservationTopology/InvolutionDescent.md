# Involution Descent

## Abstract

A transformation descends through a surjective readout exactly when it preserves readout fibers.

**Theorem 1.1 (Kernel stability is exactly existence of a descended map).**

$$\begin{gathered}\forall readout: \operatorname{Concept}\left(X, Coordinate\right), transform: X \to X,\\{}\operatorname{Surjective}\left(readout\right) \Rightarrow\\{}(\operatorname{KernelStable}\left(readout, transform\right) \iff \exists descended: Coordinate \to Coordinate, descended \circ readout = readout \circ transform).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ObservationTopology/InvolutionDescent.kernelStable_iff_exists_descended` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

KernelStable says that source points with equal readout values remain equal after transforming and reading out again.

For a surjective readout, a chosen representative of each coordinate defines a coordinate transformation. Kernel stability makes that definition independent of the representative.

Conversely, any factorization through a coordinate map carries equal readout values to equal transformed readout values.

The equivalence is conditional on surjectivity; existence through an arbitrary nonsurjective readout is not claimed.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ObservationTopology/InvolutionDescent.kernelStable_iff_exists_descended`
- Dependency: [D5/S3/ConceptDynamics/ConceptFiberDecomposition](../ConceptFiberDecomposition.md)
