# Reflection Unit Memory Residual

## Abstract

Dynamical reflection adds the current kernel modulo its maximal invariant core.

**Theorem 1.1 (The reflection unit is the canonical kernel residual).**

$$\forall K, V, W: \operatorname{Type},\\{}\operatorname{Ring}\left(K\right), \operatorname{AddCommGroup}\left(V\right), \operatorname{Module}\left(K, V\right),\\{}\operatorname{AddCommGroup}\left(W\right), \operatorname{Module}\left(K, W\right),\\{}C: \operatorname{LinearMap}\left(K, V, W\right), T: \operatorname{LinearMap}\left(K, V, V\right),\\{}\operatorname{eventualKernel}\left(C, T\right) \subseteq \operatorname{ker}\left(C\right) \land\\{}(\forall x: V, x \in \operatorname{eventualKernel}\left(C, T\right) \Rightarrow T\left(x\right) \in \operatorname{eventualKernel}\left(C, T\right)) \land\\{}(\forall M: \operatorname{Submodule}\left(K, V\right), (M \subseteq \operatorname{ker}\left(C\right) \land \forall x: V, x \in M \Rightarrow T\left(x\right) \in M) \Rightarrow M \subseteq \operatorname{eventualKernel}\left(C, T\right)) \land\\{}(\forall x: \operatorname{ker}\left(C\right), (\operatorname{QuotientMk}\left(C, T, x\right): \operatorname{memoryQuotient}\left(C, T\right)) = 0 \iff \operatorname{coe}\left(x\right) \in \operatorname{eventualKernel}\left(C, T\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/LinearMemory/ReflectionUnitMemoryResidual.reflection_unit_memory_residual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The imported eventualKernel is constructed by requiring every finite update iterate to remain in the observation kernel. It is therefore contained in the current kernel, preserved by the update, and contains every other invariant submodule of that kernel.

The imported memoryQuotient is the quotient of the current kernel by that eventual kernel viewed inside it. The final public clause exposes the canonical quotient map directly: a current-kernel direction maps to zero exactly when it belongs to the eventual kernel.

## References

- Truth anchor: `D5/S3/Observer/LinearMemory/ReflectionUnitMemoryResidual.reflection_unit_memory_residual`
- Dependency: [D5/S3/Observer/LinearMemory/ZeroMemoryCriterion](ZeroMemoryCriterion.md)
