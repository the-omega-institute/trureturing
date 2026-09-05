# Restricted-Scalar Free Minkowski Lattice

## Abstract

Free restriction of scalars has product rank and a full conjugate Minkowski lattice.

**Theorem 1.1 (All conjugate coordinates complete the finite-free module).**

$$\operatorname{degree}\left(K\right) = d \Rightarrow \operatorname{finrankZ}\left(\operatorname{freeModule}\left(K, r\right)\right) = r \times d \land \operatorname{IsZLattice}\left(\operatorname{restrictedMinkowskiLattice}\left(K, r\right)\right) \land \operatorname{IsAddFundamentalDomain}\left(\operatorname{restrictedMinkowskiLattice}\left(K, r\right), \operatorname{fundamentalDomain}\left(\operatorname{restrictedMinkowskiBasis}\left(K, r\right)\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/RestrictedScalarFreeMinkowskiLattice.restricted_scalar_free_minkowski_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a number field K of rational degree d, the free module with r coordinates over its ring of integers has integer rank r times d.

The restrictedMinkowskiEmbedding applies the mixed archimedean embedding in every coordinate. Its image is proved equal to the integer span of the product of Mathlib's Minkowski lattice bases. That equality gives discreteness, full real span, and the displayed additive fundamental domain.

The source theorem was stated for an arbitrary rank-r projective module. Pinned Mathlib has the required lattice theorem for the ring of integers and fractional ideals, but no Steinitz decomposition for arbitrary finite projective modules over that Dedekind domain. The formal statement therefore records the complete finite-free case O_K^r and does not claim the unavailable projective generalization.

Pinned Mathlib supplies RingOfIntegers.rank, finite-product finrank, the integer Minkowski lattice basis, its discrete full-rank lattice instances, and ZSpan.isAddFundamentalDomain.

## References

- Truth anchor: `D5/S3/Arith/Lattices/RestrictedScalarFreeMinkowskiLattice.restricted_scalar_free_minkowski_completion`
