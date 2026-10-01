# A Distinguished Cycle from a Parameter Word

## Abstract

A parameter permutation specifies a long cycle and a sequence of cyclic successors.

**Definition 1.1 (The distinguished long-cycle permutation).**

Lean statement: `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateCycle.P`

*Formalization.* `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateCycle.P` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Robert P. Laudone (2024). *Pattern avoidance and the fundamental bijection*. DOI: [10.48550/arXiv.2407.06338](https://doi.org/10.48550/arXiv.2407.06338). URL: <https://arxiv.org/abs/2407.06338v1>.

*Commentary.*

For a parameter word r of length h, take the inverse fundamental image of the word h plus two, followed by the letters of r each increased by one, followed by one.

**Definition 1.2 (The successor word of the parameter).**

Lean statement: `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateCycle.b`

*Formalization.* `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateCycle.b` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Robert P. Laudone (2024). *Pattern avoidance and the fundamental bijection*. DOI: [10.48550/arXiv.2407.06338](https://doi.org/10.48550/arXiv.2407.06338). URL: <https://arxiv.org/abs/2407.06338v1>.

*Commentary.*

For each x from one through the length of r, record one plus the letter following x in r, or one if x is the last letter.

**Theorem 1.3 (The successor word is a permutation).**

Lean statement: `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateCycle.b_perm_of_first_max`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateCycle.b_perm_of_first_max` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Robert P. Laudone (2024). *Pattern avoidance and the fundamental bijection*. DOI: [10.48550/arXiv.2407.06338](https://doi.org/10.48550/arXiv.2407.06338). URL: <https://arxiv.org/abs/2407.06338v1>.

*Commentary.*

If r is a permutation beginning with its maximum, its successor word b(r) permutes the same interval of integers.

## References

- Truth anchor: `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateCycle.P`
- Truth anchor: `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateCycle.b`
- Truth anchor: `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateCycle.b_perm_of_first_max`
- Dependency: [D5/S3/Combinatorics/FundamentalBijection/ThetaIterateScan](ThetaIterateScan.md)
