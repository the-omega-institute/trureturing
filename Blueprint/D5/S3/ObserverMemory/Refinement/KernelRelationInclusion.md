# Kernel Relation Inclusion

## Abstract

A refinement factorization contains the fine equality kernel in the coarse equality kernel.

**Theorem 1.1 (Refinement implies equality-kernel inclusion).**

$$\forall X, Fine, Coarse: \operatorname{Type},\\{}fine: X \to Fine, coarse: X \to Coarse,\\{}\operatorname{Refines}\left(fine, coarse\right) \Rightarrow \forall x, y: X, fine(x) = fine(y) \Rightarrow coarse(x) = coarse(y).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Refinement/KernelRelationInclusion.refinement_implies_kernel_inclusion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A refinement consists of a coarse-value map together with a commuting equation from the fine readout to the coarse one. Applying that map to equal fine values gives equal coarse values.

The formal proof imports the canonical refinement record and directly applies the existing relative-identity refinement theorem's kernel-inclusion conjunct. No parallel refinement or kernel primitive is introduced.

## References

- Truth anchor: `D5/S3/ObserverMemory/Refinement/KernelRelationInclusion.refinement_implies_kernel_inclusion`
- Dependency: [D5/S0/Rewriting/Quotients/RelativeIdentityRefinement](../../../S0/Rewriting/Quotients/RelativeIdentityRefinement.md)
- Dependency: [D5/S3/ObserverMemory/Refinement/FactorizationCategory](FactorizationCategory.md)
