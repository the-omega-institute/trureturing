# Finite Gram rank and Euclidean feature maps

## Abstract

For the reading of a ternary comparison structure, a uniform bound r on the rank of all finite Gram matrices is equivalent to the reading being the Gram kernel of a map into Euclidean r-space.

**Theorem 1.1 (Gram rank at most r and feature maps into Euclidean r-space).**

$$\forall M \in \operatorname{Type}*,\; \forall C \in \operatorname{TernaryComparison}\left(M\right),\; \forall r \in \mathbb{N},\; \operatorname{GramRankLE}\left(C, r\right) \Leftrightarrow \operatorname{HasFeatureRank}\left(C, r\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/GramRankFeatureMap.gramRankLE_iff_hasFeatureRank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* N. Aronszajn (1950). *Theory of reproducing kernels*. DOI: [10.1090/S0002-9947-1950-0051437-7](https://doi.org/10.1090/S0002-9947-1950-0051437-7).

*Commentary.*

Let C be a ternary comparison structure on M and r a natural number. The left side says that for every n and every family x : Fin n -> M the matrix with entries kappa (x i) (x j) has rank at most r. The right side says that there is a map f from M into the Euclidean space of dimension r with kappa x y equal to the real inner product of f x and f y for all x and y. If such an f exists, each Gram matrix of the reading is the Gram matrix of the vectors f (x i) in an r-dimensional space, so it factors through r coordinates and has rank at most r. Conversely, the reading is symmetric with nonnegative finite Gram forms, so it is a positive semidefinite kernel, and its reproducing kernel Hilbert space contains kernel functions k x with inner product kappa x y between k x and k y. A linearly independent family of kernel functions has an invertible Gram matrix, so by the rank bound it has at most r members. A maximal such family therefore exists, spans every kernel function, and spans a subspace of dimension at most r. Coordinates of the kernel functions in an orthonormal basis of that subspace, padded by zero coordinates up to dimension r, give the map f.

## References

- Truth anchor: `D5/S3/Quantum/AURICOmega/GramRankFeatureMap.gramRankLE_iff_hasFeatureRank`
- Dependency: [D5/S3/Quantum/AURICOmega/TernaryComparisonGroup](TernaryComparisonGroup.md)
