# Intervals within a single inflated block

## Abstract

Let a simple skeleton of size at least four be inflated at a valid position by a nonempty permutation block. Every proper nontrivial interval of the inflated permutation lies inside the inserted block. Conversely, each interval of the block with positive lower value becomes an interval at the corresponding position in the inflated permutation, with its values shifted by the skeleton entry minus one.

**Theorem 1.1 (Intervals within a single inflated block).**

Lean statement: `D5/S3/Combinatorics/PopStack/PopStackPrime.inflation_intervals`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PopStack/PopStackPrime.inflation_intervals` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lapo Cioni, Luca Ferrari, Rebecca Smith (2025). *Sorting permutations using a pop stack with a bypass*. DOI: [10.1016/j.disc.2025.114964](https://doi.org/10.1016/j.disc.2025.114964). URL: <https://arxiv.org/abs/2503.08285v1>.

*Commentary.*

Let a simple skeleton of size at least four be inflated at a valid position by a nonempty permutation block. Every proper nontrivial interval of the inflated permutation lies inside the inserted block. Conversely, each interval of the block with positive lower value becomes an interval at the corresponding position in the inflated permutation, with its values shifted by the skeleton entry minus one.

## References

- Truth anchor: `D5/S3/Combinatorics/PopStack/PopStackPrime.inflation_intervals`
- Dependency: [D5/S3/Combinatorics/PopStack/PopStackInflation](PopStackInflation.md)
