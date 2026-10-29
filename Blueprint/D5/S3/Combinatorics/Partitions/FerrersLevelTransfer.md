# Gaussian Level Transitions

## Abstract

A whole level is counted by a guarded Gaussian coefficient after its last row is fixed.

**Definition 1.1 (A prescribed level).**

Lean statement: `D5/S3/Combinatorics/Partitions/FerrersLevelTransfer.Level`

*Formalization.* `D5/S3/Combinatorics/Partitions/FerrersLevelTransfer.Level` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kenneth Barrese (2023). *Weighted File Placements on Singleton Boards*. DOI: [10.48550/arXiv.2312.10855](https://doi.org/10.48550/arXiv.2312.10855). URL: <https://arxiv.org/abs/2312.10855v1>.

*Commentary.*

Level(r,U,u,v,a) consists of all weakly decreasing tuples of r+1 row lengths in {0,...,U}, each at most u, whose last row is v and whose sum is a. The actual level size is m=r+1.

**Definition 1.2 (Explicit transition coefficient).**

Lean statement: `D5/S3/Combinatorics/Partitions/FerrersLevelTransfer.transition`

*Formalization.* `D5/S3/Combinatorics/Partitions/FerrersLevelTransfer.transition` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kenneth Barrese (2023). *Weighted File Placements on Singleton Boards*. DOI: [10.48550/arXiv.2312.10855](https://doi.org/10.48550/arXiv.2312.10855). URL: <https://arxiv.org/abs/2312.10855v1>.

*Commentary.*

For 0 <= u,v <= U, the entry T_a(u,v) is zero unless v <= u and (r+1)v <= a. Otherwise it is the coefficient of q^(a-(r+1)v) in G(u-v+r,r), the Gaussian polynomial. The polynomial G is specified by G(s,0)=1, G(0,k+1)=0, and G(s+1,k+1)=G(s,k+1)+q^(s-k)G(s,k), with natural exponents. This gives finite arithmetic evaluation for every input, including infeasible data.

**Theorem 1.3 (All fixed-endpoint levels).**

Lean statement: `D5/S3/Combinatorics/Partitions/FerrersLevelTransfer.level_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/FerrersLevelTransfer.level_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kenneth Barrese (2023). *Weighted File Placements on Singleton Boards*. DOI: [10.48550/arXiv.2312.10855](https://doi.org/10.48550/arXiv.2312.10855). URL: <https://arxiv.org/abs/2312.10855v1>.

*Commentary.*

The cardinality of Level(r,U,u,v,a) is T_a(u,v). Subtract v from the first r rows and drop the last row; this bijects the legal level with decreasing r-tuples bounded by u-v and total a-(r+1)v. Its inverse adds v and appends v. LiUncu.gauss_rectangle supplies the weight enumerator. Coefficient extraction then counts exactly the required sum fiber. If either guard fails the level is empty. For r=0 the rectangle has no entries and only exponent zero contributes.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/FerrersLevelTransfer.Level`
- Truth anchor: `D5/S3/Combinatorics/Partitions/FerrersLevelTransfer.level_card`
- Truth anchor: `D5/S3/Combinatorics/Partitions/FerrersLevelTransfer.transition`
- Dependency: [D5/S3/Combinatorics/CylindricPartition/LiUncuRectangle](../CylindricPartition/LiUncuRectangle.md)
