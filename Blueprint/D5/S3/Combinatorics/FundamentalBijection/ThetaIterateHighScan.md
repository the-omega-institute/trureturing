# The Descending High Prefix

## Abstract

The terminal value fixes the length and values of a decreasing high prefix.

**Theorem 1.1 (The high prefix values).**

Lean statement: `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateHighScan.high_prefix_descending`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateHighScan.high_prefix_descending` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Robert P. Laudone (2024). *Pattern avoidance and the fundamental bijection*. DOI: [10.48550/arXiv.2407.06338](https://doi.org/10.48550/arXiv.2407.06338). URL: <https://arxiv.org/abs/2407.06338v1>.

*Commentary.*

For a permutation r of size h at least four starting with h, h minus one, having penultimate value one and terminal value v at least two, if r and b(r) avoid 132, then the value at every position i below h minus v is h minus i.

## References

- Truth anchor: `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateHighScan.high_prefix_descending`
- Dependency: [D5/S3/Combinatorics/FundamentalBijection/ThetaIterateFirstScan](ThetaIterateFirstScan.md)
