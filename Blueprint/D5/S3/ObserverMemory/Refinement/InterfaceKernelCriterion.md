# Interface Kernel Criterion

## Abstract

Interface refinement is exactly reverse inclusion of equality kernels.

**Theorem 1.1 (Interface refinement is equivalent to kernel inclusion).**

$$\forall X, A, B: \operatorname{Type},\\{}q: X \to A, r: X \to B,\\{}(\exists! h: \operatorname{range}(r) \to \operatorname{range}(q), \forall x: X, h(\operatorname{rangeFactorization}(r, x)) = \operatorname{rangeFactorization}(q, x)) \Leftrightarrow (\forall x, y: X, r(x) = r(y) \Rightarrow q(x) = q(y)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Refinement/InterfaceKernelCriterion.interface_refinement_iff_kernel_inclusion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let q and r be interfaces on a shared state carrier, with their codomains restricted canonically to realized images.

The interface q is refined by r precisely when there is a unique factor from range(r) to range(q) commuting with the canonical range factorizations. This is equivalent to equality under r always implying equality under q.

The proof directly applies the exact observer-memory effective-image kernel criterion, retaining both directions and uniqueness in the public statement.

## References

- Truth anchor: `D5/S3/ObserverMemory/Refinement/InterfaceKernelCriterion.interface_refinement_iff_kernel_inclusion`
- Dependency: [D5/S3/ObserverMemory/Refinement/EffectiveImageKernelCriterion](EffectiveImageKernelCriterion.md)
