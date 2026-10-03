# Bounds from the Parameter Cycle

## Abstract

Avoidance in a parameter, its successor word, and its cycle word controls the terminal value and low suffix.

**Theorem 1.1 (A lower bound for the terminal value).**

Lean statement: `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateCycleScan.terminal_value_at_least_half`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateCycleScan.terminal_value_at_least_half` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Robert P. Laudone (2024). *Pattern avoidance and the fundamental bijection*. DOI: [10.48550/arXiv.2407.06338](https://doi.org/10.48550/arXiv.2407.06338). URL: <https://arxiv.org/abs/2407.06338v1>.

*Commentary.*

Let r and q be permutations of the same size h at least four, with q beginning at h and its cyclic successor map equal to the permutation map of r. If r starts with h, h minus one, has penultimate value one and terminal value v at least two, and r, b(r), and q all avoid 132, then h is at most twice v.

**Theorem 1.2 (The decreasing low suffix).**

Lean statement: `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateCycleScan.low_suffix_descending`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateCycleScan.low_suffix_descending` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Robert P. Laudone (2024). *Pattern avoidance and the fundamental bijection*. DOI: [10.48550/arXiv.2407.06338](https://doi.org/10.48550/arXiv.2407.06338). URL: <https://arxiv.org/abs/2407.06338v1>.

*Commentary.*

Under the same cycle and avoidance conditions, if v is below h minus two, then the entry of r at each position i from v through h minus three is h minus one minus i.

## References

- Truth anchor: `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateCycleScan.low_suffix_descending`
- Truth anchor: `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateCycleScan.terminal_value_at_least_half`
- Dependency: [D5/S3/Combinatorics/FundamentalBijection/ThetaIterateHighScan](ThetaIterateHighScan.md)
