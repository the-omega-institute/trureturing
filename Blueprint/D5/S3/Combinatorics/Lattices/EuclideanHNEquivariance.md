# Saturated sublattices and Gram covolumes

## Abstract

Isometries of the Euclidean Harder-Narasimhan filtration

Let E be a finite-dimensional real inner product space, L a discrete integral submodule, and T a linear isometric automorphism with T(L) equal to L. The lattice need not span E. The zero lattice and the rank-zero stages are included.

**Theorem 1.1 (Every HN stage is fixed by every integral isometry).**

Lean statement: `D5/S3/Combinatorics/Lattices/EuclideanHNEquivariance.isometry_hn`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Lattices/EuclideanHNEquivariance.isometry_hn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel R. Grayson (1984). *Reduction theory using semistability*. DOI: [10.1007/BF02566369](https://doi.org/10.1007/BF02566369).

*Commentary.*

The restriction of T to L is an integral linear automorphism. Mapping an integral submodule through this automorphism commutes with taking its real span and with taking all lattice points in that span. It therefore induces an order automorphism of the saturated sublattices. Its ambient carrier is exactly the image under T.

An integral basis maps to an integral basis of the image. The displayed right-hand Gram square root is the defining covolume of the original sublattice. The corresponding Gram matrices agree entry by entry because T preserves inner products. Thus every saturated sublattice has the same rank and covolume as its image, and every quotient interval has the same slope. Semistability and the strict decrease of factor slopes are preserved, so the image of any HN chain is an HN chain between the image endpoints. Conversely, an HN chain on the image list implies that the original endpoints are ordered. Transport the unique original HN chain and compare it with the image chain by uniqueness. Injectivity of the isometry on lists recovers the original chain. Thus HN filtration is equivalent to HN filtration of the image list between the image endpoints.

For any interval whose endpoints are fixed, including the zero sublattice to L, uniqueness of the Euclidean HN filtration makes the image endpoint list equal to the original list. Equality is position by position, so every stage is fixed. For every real t, the consecutive factors of slope strictly greater than t define a fixed saturated sublattice as well. The comparison is strict, including when a factor slope equals t.

This construction and its concrete covariance proof are repo-derived from the existing Gram-covolume and HN uniqueness results. No finiteness assumption on a group of isometries is required: the conclusion applies to every lattice-preserving isometry separately, and hence to every stage under any such group action.

## References

- Truth anchor: `D5/S3/Combinatorics/Lattices/EuclideanHNEquivariance.isometry_hn`
- Dependency: [D5/S3/Combinatorics/Lattices/EuclideanHarderNarasimhan](EuclideanHarderNarasimhan.md)
