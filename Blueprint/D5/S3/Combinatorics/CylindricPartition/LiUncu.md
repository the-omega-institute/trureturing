# The Finite Andrews-Gordon Companion Identity

## Abstract

Li and Uncu's finite Andrews-Gordon companion identity holds for every k at least five.

**Theorem 1.1 (The companion identity).**

Lean statement: `D5/S3/Combinatorics/CylindricPartition/LiUncu.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CylindricPartition/LiUncu.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Runqiao Li, Ali K. Uncu (2025). *A MacMahon Analysis View of Cylindric Partitions*. DOI: [10.48550/arXiv.2501.19272](https://doi.org/10.48550/arXiv.2501.19272). URL: <https://arxiv.org/abs/2501.19272v1>.

*Commentary.*

For every nonnegative integer n, every integer k at least five, and every integer i with 1 at most i and i less than k, the finite multiple sum equals the finite alternating Gaussian sum of equation (1.5). The multiple sum runs over n_1 at least n_2 at least the successive entries through n_(k-1) at least n_k = 0, with entries at most n. Its exponent is the sum of n_j squared for 1 at most j and j less than k, plus the sum of n_j for i at most j and j less than k. Its jth primed Gaussian factor has upper index 2n - 2 times the sum of n_l for l less than j, minus n_j, n_(j+1), and 2 max(j-i+1,0), and lower index n_j - n_(j+1). The alternating sum has sign (-1)^r, exponent r((2k+1)r+2k-2i+1)/2, and Gaussian upper index 2n and lower index n-(2k+1)r/2+(2k-2i+1)((-1)^r-1)/4. Its nonzero terms have r between -(n+1) and n+1. The Gaussian polynomial vanishes outside zero through its upper index; its primed version is one at lower index zero even for a negative upper index. Weighted peak deletion gives the multiple sum, and the four image families give the alternating sum.

## References

- Truth anchor: `D5/S3/Combinatorics/CylindricPartition/LiUncu.result`
- Dependency: [D5/S3/Combinatorics/CylindricPartition/LiUncuImages](LiUncuImages.md)
