# Low Entries in the Forced Prefix

## Abstract

The prescribed boundary data for two consecutive inverse images determine additional small entries.

**Theorem 1.1 (Four forced small entries).**

Lean statement: `D5/S3/Combinatorics/FundamentalBijection/ThetaCube231LargePrefix.forced_low_prefix`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FundamentalBijection/ThetaCube231LargePrefix.forced_low_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Robert P. Laudone (2024). *Pattern avoidance and the fundamental bijection*. DOI: [10.48550/arXiv.2407.06338](https://doi.org/10.48550/arXiv.2407.06338). URL: <https://arxiv.org/abs/2407.06338v1>.

*Commentary.*

Let p and q be permutations of size n at least eleven with p avoiding 231, q the inverse image of p, and the second inverse image of q equal to p. Suppose p starts with n, one, n minus two, two and ends with n minus one, while q has n minus two, n minus one, n, one at positions zero, n minus four, n minus two, n minus one. Then q has four and three at positions one and three, and p has four and three at positions four and five.

## References

- Truth anchor: `D5/S3/Combinatorics/FundamentalBijection/ThetaCube231LargePrefix.forced_low_prefix`
- Dependency: [D5/S3/Combinatorics/FundamentalBijection/ThetaBasicInverse](ThetaBasicInverse.md)
- Dependency: [D5/S3/Combinatorics/FundamentalBijection/ThetaBasicInverseTail](ThetaBasicInverseTail.md)
