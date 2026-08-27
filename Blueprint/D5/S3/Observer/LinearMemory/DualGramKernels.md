# Dual Gram Kernels

## Abstract

The two Gram kernels equal the observation and adjoint kernels.

**Theorem 1.1 (The state and protocol Gram kernels are exact).**

$$\begin{aligned}\forall K, V, iota: \operatorname{Type},\\{}[\operatorname{RCLike}(K)], [\operatorname{NormedAddCommGroup}(V)], [\operatorname{InnerProductSpace}(K, V)],\\{}[\operatorname{FiniteDimensional}(K, V)], [\operatorname{Fintype}(iota)],\\\forall ell: iota \to \operatorname{LinearMap}(K, V, K),\\{}let M: \operatorname{LinearMap}(K, V, \operatorname{PiLp}(2, iota \to K)) = \operatorname{comp}(\operatorname{toLinearMap}(\operatorname{symm}(\operatorname{withLpLinearEquiv}(2, K, iota \to K))), \operatorname{linearPi}(ell));\\\operatorname{ker}(\operatorname{comp}(\operatorname{adjoint}(M), M)) = \operatorname{ker}(M) \land\\{}\operatorname{ker}(\operatorname{comp}(M, \operatorname{adjoint}(M))) = \operatorname{ker}(\operatorname{adjoint}(M)).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/LinearMemory/DualGramKernels.dual_gram_kernels` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a finite indexed family assign a scalar linear readout to every protocol. The observation map is constructed coordinatewise on the same square-summable protocol carrier as the visible-range companion.

The kernel of the adjoint-observation composition is exactly the unseen state kernel. Reversing the composition gives exactly the kernel of the adjoint, which records redundant protocol combinations.

Both clauses directly apply the pinned library's exact finite-dimensional adjoint-composition kernel lemmas.

## References

- Truth anchor: `D5/S3/Observer/LinearMemory/DualGramKernels.dual_gram_kernels`
- Dependency: [D5/S3/Observer/LinearMemory/DualGramVisibleRanges](DualGramVisibleRanges.md)
