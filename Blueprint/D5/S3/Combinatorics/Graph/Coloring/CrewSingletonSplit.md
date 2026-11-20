# Positive singleton-split coefficients

## Abstract

A beta-integral estimate bounds the singleton-split coefficient.

**Definition 1.1 (The weight of a marked split).**

Lean statement: `D5/S3/Combinatorics/Graph/Coloring/CrewSingletonSplit.weight`

*Formalization.* `D5/S3/Combinatorics/Graph/Coloring/CrewSingletonSplit.weight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Lila Crew, Benjamin Keller, Katharina Kuehr, Shao Yuan Lin, Megan Ixchel Monroy Rodríguez, Tabitha Williams (2026). *Properties of the Dichromatic Polynomial*. DOI: [10.48550/arXiv.2611.13273](https://doi.org/10.48550/arXiv.2611.13273). URL: <https://arxiv.org/abs/2611.13273v1>.

*Commentary.*

For a finite set of other blocks with natural sizes, a natural marked block size r, and a real palette parameter x, start with the falling factorial of x − 1 of length equal to the number of other blocks. Subtract the sum over subsets of other blocks. Each summand is the falling factorial of x of length equal to the number of blocks outside the subset, multiplied by the factorial of the subset size and its alternating sign, and divided by r plus the sum of the sizes in the subset.

**Theorem 1.2 (A positive lower bound).**

Lean statement: `D5/S3/Combinatorics/Graph/Coloring/CrewSingletonSplit.weight_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Coloring/CrewSingletonSplit.weight_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lila Crew, Benjamin Keller, Katharina Kuehr, Shao Yuan Lin, Megan Ixchel Monroy Rodríguez, Tabitha Williams (2026). *Properties of the Dichromatic Polynomial*. DOI: [10.48550/arXiv.2611.13273](https://doi.org/10.48550/arXiv.2611.13273). URL: <https://arxiv.org/abs/2611.13273v1>.

*Commentary.*

If the marked block has at least two elements, every other block has positive size, and x is at least the total size minus one, the weight is at least the falling factorial of x − 1 of length equal to the number of other blocks divided by x + 1. The weight is strictly positive. A beta-moment identity turns the signed sum into an integral. A product estimate bounds that integral on the unit interval.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Coloring/CrewSingletonSplit.weight`
- Truth anchor: `D5/S3/Combinatorics/Graph/Coloring/CrewSingletonSplit.weight_bounds`
