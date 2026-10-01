# Interleaving Along a Step Sequence

## Abstract

Upsteps and downsteps select the two occurrence orders of a doubled word.

**Definition 1.1 (Interleaving two lists).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalEncoding.weave`

*Formalization.* `D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalEncoding.weave` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

Traverse a step sequence, taking the next letter of the first list at each upstep and the next letter of the second list at each downstep. The interleaving is defined exactly when the traversal consumes both lists and the entire step sequence.

**Definition 1.2 (Selection by step type).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalEncoding.select`

*Formalization.* `D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalEncoding.select` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sergi Elizalde, Amya Luo (2024). *Pattern avoidance in nonnesting permutations*. DOI: [10.48550/arXiv.2412.00336](https://doi.org/10.48550/arXiv.2412.00336). URL: <https://arxiv.org/abs/2412.00336v6>.

*Commentary.*

Traverse a step sequence and a letter list together, retaining precisely the letters paired with the chosen step type and stopping when either list is exhausted.

## References

- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalEncoding.select`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalEncoding.weave`
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingBasicOrders](NonnestingBasicOrders.md)
