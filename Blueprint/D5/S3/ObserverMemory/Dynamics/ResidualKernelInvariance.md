# Residual Kernel Invariance

## Abstract

Adjoint invariance of an observable subspace preserves its orthogonal residual.

**Theorem 1.1 (Adjoint invariance preserves the orthogonal residual).**

$$\forall k, E: \operatorname{Type},\ [\operatorname{RCLike}(k)],\ [\operatorname{CompleteInnerProductSpace}_{k}(E)],\ T: \operatorname{ContinuousLinearEnd}(k, E),\ S: \operatorname{Submodule}(k, E),\ \operatorname{map}(\operatorname{adjoint}(T), S) \subseteq S \Rightarrow \operatorname{map}(T, S^{\perp}) \subseteq S^{\perp}.$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Dynamics/ResidualKernelInvariance.residual_kernel_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E be a complete real or complex inner-product space, let T be a continuous linear endomorphism, and let S be a subspace. If the adjoint of T maps S into S, then T maps the orthogonal complement of S into itself.

Pinned Mathlib supplies the exact general result ContinuousLinearMap.orthogonal_mem_invtSubmodule. The Lean proof translates setwise preservation into invariant-submodule membership, applies that result, and translates back. Loogle's exact-name query returned the declaration as its single hit; the repository's local phrase search returned no declaration-name hit.

This covers only the orthogonal-complement step inside qdo-v1 theorem/28.22, atom qdo-residual-7e47cd0779d95fbf6cd811d632df752946939c179a0ae2d17371fdc9d5b6d0e5. It does not assert the filtration equivalence, reducing invariance of every shell or final residual, or vanishing of all off-diagonal blocks.

## References

- Truth anchor: `D5/S3/ObserverMemory/Dynamics/ResidualKernelInvariance.residual_kernel_invariant`
