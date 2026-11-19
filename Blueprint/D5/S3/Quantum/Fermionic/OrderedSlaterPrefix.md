# Slater determinant marginals at an ordered cut

## Abstract

Slater determinant marginals at an ordered cut

**Theorem 1.1 (The full product spectrum at an ordered prefix).**

Lean statement: `D5/S3/Quantum/Fermionic/OrderedSlaterPrefix.prefix_product_spectrum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/OrderedSlaterPrefix.prefix_product_spectrum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a matrix with orthonormal columns on a consecutive site order, the marginal on the first m sites has the complete product spectrum determined by the retained compression. The characteristic polynomial includes all occupation labels and all multiplicities.

**Theorem 1.2 (Cut classification for the full Slater product spectrum).**

$$\begin{aligned}\forall \iota: \operatorname{Type}, [\operatorname{LinearOrder}(\iota)] [\operatorname{Fintype}(\iota)], I: \operatorname{Set}(\iota),\\\neg\operatorname{Alternates}(I) \iff \forall k \in \mathbb{N}, V: \operatorname{Matrix}(\iota, \operatorname{Fin}(k), \mathbb{C}),\\V^{*}V=1 \longrightarrow \operatorname{HasProductSpectrum}(I, V)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/OrderedSlaterPrefix.universal_cut_product_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a prefix, a unitary change of basis on the retained site rows acts by the corresponding ordered minors in each retained particle-number sector. These sector matrices are unitary by Cauchy–Binet, so the full marginal characteristic polynomial is invariant. Diagonalize the retained compression. The weighted Cauchy–Binet formula for determinant contractions then gives the diagonal occupation weights. Equality of the compression characteristic polynomials allows any relabeling of the mode values, including repeated and zero eigenvalues. For a cut without four alternating sites, the fixed-occupation shuffle and the stable ordering of the sides reduce the problem to the prefix. At either alternating order, two occupied orbitals give two ordinary marginal eigenvalues of one half while the product spectrum has a single nonzero eigenvalue of one.

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/OrderedSlaterPrefix.prefix_product_spectrum`
- Truth anchor: `D5/S3/Quantum/Fermionic/OrderedSlaterPrefix.universal_cut_product_iff`
- Dependency: [D5/S3/Quantum/Fermionic/OrderedSlaterCut](OrderedSlaterCut.md)
- Dependency: [D5/S3/Quantum/Fermionic/SlaterPrefixContraction](SlaterPrefixContraction.md)
