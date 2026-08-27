# Unique Interface Kernel Criterion

## Abstract

Unique effective-interface factorization is reverse kernel inclusion.

**Theorem 1.1 (A unique interface factor exists exactly under reverse kernel inclusion).**

$$\begin{gathered}\forall X, Bq, Br: \operatorname{Type},\\{}q: X \to Bq, r: X \to Br,\\{}\operatorname{Surjective}(r) \Rightarrow\\{}(\exists! pi: Br \to Bq, q = pi \circ r) \Leftrightarrow (\operatorname{ker}(r) \subseteq \operatorname{ker}(q)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Factor/UniqueInterfaceKernelCriterion.unique_interface_factorization_iff_reverse_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finer readout is surjective onto its declared carrier, matching the effective-interface convention. The factor and its commuting equation are exposed publicly with uniqueness.

The imported canonical theorem gives existence exactly from reverse kernel inclusion. Surjectivity then makes any two factors agree on every finer-interface value.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Factor/UniqueInterfaceKernelCriterion.unique_interface_factorization_iff_reverse_kernel`
- Dependency: [D5/S3/ConceptDynamics/RefinementAlgebra/ObserverStrategyFactorization](../RefinementAlgebra/ObserverStrategyFactorization.md)
