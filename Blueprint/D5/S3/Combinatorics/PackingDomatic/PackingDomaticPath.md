# A Negative Answer to Problem 2

## Abstract

The path on 56 vertices refutes the proposed bound for packing 28-domatic colourings.

**Theorem 1.1 (Some paths require more than k+1 colours).**

$$\neg (claim)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PackingDomatic/PackingDomaticPath.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Boštjan Brešar, Jasmina Ferme, Wenjie Hu (2026). *Partitioning an S-packing coloring into broadcast dominating sets*. DOI: [10.48550/arXiv.2610.03477](https://doi.org/10.48550/arXiv.2610.03477). URL: <https://arxiv.org/abs/2610.03477v1>.

*Commentary.*

Take k=28 and n=56. A packing 28-domatic colouring using colours at most 29 would satisfy the counting bound, since 30 is at most 56. That bound would require 448 to be at most 447, a contradiction. Thus P_56 has no such colouring, and the proposed bound fails despite k being at least 3 and n being at least 2k.

## References

- Truth anchor: `D5/S3/Combinatorics/PackingDomatic/PackingDomaticPath.result`
- Dependency: [D5/S3/Combinatorics/PackingDomatic/PackingDomaticPathCounting](PackingDomaticPathCounting.md)
