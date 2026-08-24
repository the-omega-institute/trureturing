# Effective Image Kernel Criterion

## Abstract

Refinement on realized images is exactly reverse inclusion of equality kernels.

**Theorem 1.1 (Effective-image refinement is equivalent to kernel inclusion).**

$$\forall X, A, B: \operatorname{Type},\\{}q: X \to A, r: X \to B,\\{}(\exists! h: \operatorname{range}(r) \to \operatorname{range}(q), \forall x: X, h(\operatorname{rangeFactorization}(r, x)) = \operatorname{rangeFactorization}(q, x)) \Leftrightarrow (\forall x, y: X, r(x) = r(y) \Rightarrow q(x) = q(y)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Refinement/EffectiveImageKernelCriterion.refinement_iff_kernel_inclusion_on_effective_images` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let q and r be readouts on the same state carrier. Refinement is stated directly on their realized codomains: there is a unique map from range(r) to range(q) commuting with both canonical range factorizations.

Any such factor sends equal r-values to equal q-values. Conversely, if equality under r always implies equality under q, selecting a source representative of each realized r-value constructs the factor, and kernel inclusion makes that construction independent of the representative.

The proof directly reuses Set.rangeFactorization, Set.rangeSplitting, and their exact computation lemmas. The existing refinement family supplies the canonical Concept carrier; no parallel readout or refinement structure is declared.

## References

- Truth anchor: `D5/S3/ObserverMemory/Refinement/EffectiveImageKernelCriterion.refinement_iff_kernel_inclusion_on_effective_images`
- Dependency: [D5/S3/ObserverMemory/Refinement/FactorizationCategory](FactorizationCategory.md)
