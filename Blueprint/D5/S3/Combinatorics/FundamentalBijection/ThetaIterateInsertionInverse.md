# Recovering a Smaller Cycle from Insertion

## Abstract

The prescribed boundary shape of an inverse image permits removal of three letters.

**Theorem 1.1 (The recovered inner permutation).**

Lean statement: `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateInsertionInverse.insertion_cycle_inverse`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateInsertionInverse.insertion_cycle_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Robert P. Laudone (2024). *Pattern avoidance and the fundamental bijection*. DOI: [10.48550/arXiv.2407.06338](https://doi.org/10.48550/arXiv.2407.06338). URL: <https://arxiv.org/abs/2407.06338v1>.

*Commentary.*

For a permutation w of size n at least five beginning with n whose inverse image begins with n, n minus one and ends with one, n minus two, there is a permutation q of size n minus three beginning with n minus three and ending with one such that I of the inverse image of q is the inverse image of w. That inverse image of q is a first-maximum permutation whose fundamental image and cycle from its maximum are q; if w avoids 132, then q avoids 132.

## References

- Truth anchor: `D5/S3/Combinatorics/FundamentalBijection/ThetaIterateInsertionInverse.insertion_cycle_inverse`
- Dependency: [D5/S3/Combinatorics/FundamentalBijection/ThetaIterateInsertionCycle](ThetaIterateInsertionCycle.md)
- Dependency: [D5/S3/Combinatorics/FundamentalBijection/ThetaIterateLastEndpoint](ThetaIterateLastEndpoint.md)
