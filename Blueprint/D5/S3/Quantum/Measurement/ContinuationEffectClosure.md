# Finite Closure of Continuation Effect Spaces

## Abstract

Starting from an r-dimensional real space of Hermitian d by d matrices, the spaces closed step by step under the duals of an arbitrary family of branches, each with a finite Kraus family, stop growing after d^2 - r steps, at the least space that contains the start and is invariant under every branch dual.

**Definition 1.1 (Branch duals).**

$$\phi_{j}^{*}(H) = \sum_{k} K_{j k}^{*} H K_{j k}$$

*Formalization.* `D5/S3/Quantum/Measurement/ContinuationEffectClosure.branchDual` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The branch j acts by the finite Kraus family K_{jk}; its dual acts on effects as above and is real linear.

**Definition 1.2 (Continuation effect spaces).**

$$Z_{n+1} = \operatorname{span}_{\mathbb{R}}(Z_{n} \cup \phi_{j}^{*}(Z_{n}) \text{ for all }j)$$

*Formalization.* `D5/S3/Quantum/Measurement/ContinuationEffectClosure.continuationSpace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each step adds the images of the current space under every branch dual.

**Theorem 1.3 (Finite closure and minimality).**

$$Z_{0} \subseteq \operatorname{Herm}(d), \operatorname{dim} Z_{0} = r \Rightarrow\\{}\forall n \geq d^{2}-r, Z_{n} = Z_{d^{2}-r},\quad Z_{0} \subseteq Z_{d^{2}-r},\quad \forall j, \phi_{j}^{*}(Z_{d^{2}-r}) \subseteq Z_{d^{2}-r},\\{}\forall W, Z_{0} \subseteq W \land (\forall j, \phi_{j}^{*}(W) \subseteq W) \Rightarrow Z_{d^{2}-r} \subseteq W.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/ContinuationEffectClosure.continuationSpace_closure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Z_0 be a real space of Hermitian d by d matrices of dimension r. If Z_{k+1} = Z_k, then Z_k is invariant under every branch dual and all later spaces equal it. Branch duals preserve Hermiticity, so every Z_k lies in the real space of Hermitian d by d matrices, which has dimension d^2; hence every Z_k has real dimension at most d^2. If the chain still grew at step d^2 - r, all earlier steps would be strict and the dimension would exceed d^2. Finally, every invariant space W containing Z_0 contains each Z_k by induction.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/ContinuationEffectClosure.branchDual`
- Truth anchor: `D5/S3/Quantum/Measurement/ContinuationEffectClosure.continuationSpace`
- Truth anchor: `D5/S3/Quantum/Measurement/ContinuationEffectClosure.continuationSpace_closure`
- Dependency: [D5/S3/Quantum/Entanglement/BipartiteSectorDecomposition](../Entanglement/BipartiteSectorDecomposition.md)
- Dependency: [D5/S3/Quantum/PredictionDepth/FiniteSequentialWordCertificate](../PredictionDepth/FiniteSequentialWordCertificate.md)
