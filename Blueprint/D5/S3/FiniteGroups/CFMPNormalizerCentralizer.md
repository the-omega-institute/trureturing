# Normalizer Quotient and Right-Coset Centralizer

## Abstract

The normalizer quotient acts as the full centralizer of the right-coset action.

**Theorem 1.1 (The generic right-coset centralizer theorem).**

$$\forall G \in Typeu,\; Group\left(G\right) \to \left(\forall H \in Subgroup\left(G\right),\; MulEquiv\left(quotientGroup\left(normalizer\left(H\right), subgroupOf\left(H, normalizer\left(H\right)\right)\right), centralizerOfRightTranslations\left(rightCosetQuotient\left(H\right), G\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/CFMPNormalizerCentralizer.normalizerCentralizerIso` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an arbitrary group G and subgroup H, Omega_R is the quotient by QuotientGroup.rightRel H and R_a sends H g to H g a. The quotient group is formed inside the normalizer N_G(H), with normality of H there derived from the normalizer definition.

The isomorphism sends n H to F_n, where F_n(H g) = H n g. Standard function composition gives F_n composed with F_m = F_(n m). An equivariant permutation is determined by its value at H; exact stabilizer preservation forces that value to be H n with n in the normalizer. An element of H acts trivially on every right coset; conversely, evaluating a kernel element at H proves that it lies in H. Thus H.subgroupOf(N_G(H)) equals the kernel of normalizerMap. QuotientGroup.liftEquiv applies directly to this kernel equality and the surjectivity of normalizerMap to give the isomorphism.

The theorem is the generic algebraic consumer for CFMP source clauses 122.2 and 123.1. It does not claim the concrete A5 marked Phi, the U,V,D arrays, a normalizer cardinality, or any topology.

## References

- Truth anchor: `D5/S3/FiniteGroups/CFMPNormalizerCentralizer.normalizerCentralizerIso`
