# Realized-Image Kernel Factorization

## Abstract

Realized-image factorization is unique exactly under reverse kernel inclusion.

**Theorem 1.1 (Realized-image factorization is the reverse kernel criterion).**

$$\begin{gathered}\forall X, A, B: \operatorname{Type},\\{}q: X \to A, r: X \to B,\\{}(\exists! h: \operatorname{range}(r) \to \operatorname{range}(q), \operatorname{rangeFactorization}(q) = h \circ \operatorname{rangeFactorization}(r)) \Leftrightarrow (\operatorname{ker}(r) \subseteq \operatorname{ker}(q)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/RefinementFactorization/RealizedImageKernelFactorization.realized_image_unique_factorization_iff_reverse_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two readouts are restricted canonically to their realized codomains by Set.rangeFactorization. The public factor is unique and its commuting equation is stated directly.

The existence equivalence is obtained by applying the imported effective_refines_iff_reverse_kernel theorem to those two surjective readouts. Their kernels are identified with the original equality kernels by the pinned Mathlib equality API.

Surjectivity of the finer range factorization then forces any two commuting factors to agree on every realized value. No parallel refinement or kernel-inclusion criterion is reconstructed.

## References

- Truth anchor: `D5/S3/ConceptDynamics/RefinementFactorization/RealizedImageKernelFactorization.realized_image_unique_factorization_iff_reverse_kernel`
- Dependency: [D5/S3/ConceptDynamics/Refinement/ConceptKernelOrderDuality](../Refinement/ConceptKernelOrderDuality.md)
