# Global, Discriminant, and Split Relations

## Abstract

Global equivalence refines discriminant equivalence, which refines split equivalence.

**Theorem 1.1 (The promised relation direction).**

$$\forall X, G, D, S: \operatorname{Type},\\{}global: X \to G, discriminant: X \to D, split: X \to S,\\{}\operatorname{Refines}(discriminant, global) \land \operatorname{Refines}(split, discriminant)\\{}\Rightarrow \operatorname{ker}(global) \subseteq \operatorname{ker}(discriminant) \land \operatorname{ker}(discriminant) \subseteq \operatorname{ker}(split).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ObservationOrder/GlobalDiscriminantSplitKernelChain.global_discriminant_split_kernel_chain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The three public relations are constructed as the equality kernels of the global classifier, discriminant readout, and split readout on one common state carrier.

Preservation of the discriminant is expressed by its factorization through the global classifier. Dependence of the split result only on the discriminant is the second canonical refinement.

Applying kernel monotonicity to those two factorizations gives the stated chain. No claim of local equivalence, genus equivalence, spinor-genus equivalence, or class-group identification is inferred.

Repository and pinned-library searches found no exact theorem packaging both inclusions. The proof applies the existing single-step relative identity refinement theorem twice.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ObservationOrder/GlobalDiscriminantSplitKernelChain.global_discriminant_split_kernel_chain`
- Dependency: [D5/S0/Rewriting/Quotients/RelativeIdentityRefinement](../../../S0/Rewriting/Quotients/RelativeIdentityRefinement.md)
- Dependency: [D5/S3/ConceptDynamics/ConceptJoinUniversal](../ConceptJoinUniversal.md)
