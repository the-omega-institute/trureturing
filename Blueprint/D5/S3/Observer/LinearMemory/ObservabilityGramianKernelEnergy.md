# Observability Gramian Kernel and Energy

## Abstract

The stable ordinary observability Gramian has the all-future readout kernel, its quadratic form is total future output energy, and that energy vanishes exactly on states with no future output.

**Theorem 1.1 (The ordinary Gramian kernel is the all-future kernel).**

$$\begin{aligned}\forall K, V, Y: \operatorname{Type},\\{}[\operatorname{RCLike}(K)], [\operatorname{NormedAddCommGroup}(V)],\\{}[\operatorname{InnerProductSpace}(K, V)], [\operatorname{FiniteDimensional}(K, V)],\\{}[\operatorname{NormedAddCommGroup}(Y)], [\operatorname{InnerProductSpace}(K, Y)],\\{}[\operatorname{FiniteDimensional}(K, Y)],\\\forall T: \operatorname{LinearMap}(K, V, V), C: \operatorname{LinearMap}(K, V, Y),\\{}hStable: \operatorname{Summable}(k \mapsto \operatorname{discountedGramianTerm}(T, C, 1, k)),\\\operatorname{ker}(\operatorname{toLinearMap}(\operatorname{discountedObservabilityGramian}(T, C, 1))) = \operatorname{intersection}_{k \in \mathbb{N}} \operatorname{ker}(\operatorname{comp}(C, T^{k})) \land\\{}(\forall x: V, \Re(\langle x, \operatorname{discountedObservabilityGramian}(T, C, 1)(x) \rangle) = \sum_{k=0}^{\infty} \left\lVert C(T^{k}(x)) \right\rVert^{2}) \land\\{}(\forall x: V, \Re(\langle x, \operatorname{discountedObservabilityGramian}(T, C, 1)(x) \rangle) = 0 \iff \forall k: \mathbb{N}, C(T^{k}(x)) = 0).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/LinearMemory/ObservabilityGramianKernelEnergy.observability_gramian_kernel_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The ordinary Gramian is the canonical weight-one instance of the repository's Gramian series. Stability is stated directly as summability of that exact operator series, without imposing a stronger contraction-norm condition.

Continuous evaluation, inner product, and real-part maps carry the summable operator series term by term. Each term is the squared norm of one future readout, so nonnegativity makes zero total energy equivalent to vanishing at every future time.

## References

- Truth anchor: `D5/S3/Observer/LinearMemory/ObservabilityGramianKernelEnergy.observability_gramian_kernel_energy`
- Dependency: [D5/S3/Observer/Linear/DiscountedObservabilityGramianPositivity](../Linear/DiscountedObservabilityGramianPositivity.md)
- Dependency: [D5/S3/ObserverMemory/Dynamics/MaximalUnobservableSubspace](../../ObserverMemory/Dynamics/MaximalUnobservableSubspace.md)
