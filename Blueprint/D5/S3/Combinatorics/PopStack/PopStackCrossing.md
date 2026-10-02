# An interval crossing a fixed gap

## Abstract

Let p be a non-simple permutation in C such that every proper nontrivial interval crosses a fixed gap strictly and has minimum value greater than one. There is a proper nontrivial interval containing every such interval. Contracting it gives a simple skeleton in C occurring in p, and standardizing its entries gives a block. Inflating that skeleton by this block recovers p. If the block has length m, the skeleton has length equal to the length of p minus m plus one.

**Theorem 1.1 (An interval crossing a fixed gap).**

Lean statement: `D5/S3/Combinatorics/PopStack/PopStackCrossing.crossing_decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PopStack/PopStackCrossing.crossing_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lapo Cioni, Luca Ferrari, Rebecca Smith (2025). *Sorting permutations using a pop stack with a bypass*. DOI: [10.1016/j.disc.2025.114964](https://doi.org/10.1016/j.disc.2025.114964). URL: <https://arxiv.org/abs/2503.08285v1>.

*Commentary.*

Let p be a non-simple permutation in C such that every proper nontrivial interval crosses a fixed gap strictly and has minimum value greater than one. There is a proper nontrivial interval containing every such interval. Contracting it gives a simple skeleton in C occurring in p, and standardizing its entries gives a block. Inflating that skeleton by this block recovers p. If the block has length m, the skeleton has length equal to the length of p minus m plus one.

## References

- Truth anchor: `D5/S3/Combinatorics/PopStack/PopStackCrossing.crossing_decomposition`
- Dependency: [D5/S3/Combinatorics/PopStack/PopStackReconstruction](PopStackReconstruction.md)
