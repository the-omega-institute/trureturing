# A strict counterexample to the mean-order comparison

## Abstract

Grouping intervals by their attachment marks evaluates each of the four moments and gives the exact rational difference between the two means.

**Definition 1.1 (Count and total order).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Summation.CountOrder`

*Formalization.* `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Summation.CountOrder` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Stijn Cambie; Jorik Jooken; Stephan Wagner (2026). *On the extrema of the mean subtree order of graphs*. DOI: [10.48550/arXiv.2508.20593](https://doi.org/10.48550/arXiv.2508.20593). URL: <https://arxiv.org/abs/2508.20593v2>.

*Commentary.*

Each pair stores a natural count and a natural sum of vertex orders.

**Definition 1.2 (The configuration moments).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Summation.codeMoments`

*Formalization.* `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Summation.codeMoments` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Stijn Cambie; Jorik Jooken; Stephan Wagner (2026). *On the extrema of the mean subtree order of graphs*. DOI: [10.48550/arXiv.2508.20593](https://doi.org/10.48550/arXiv.2508.20593). URL: <https://arxiv.org/abs/2508.20593v2>.

*Commentary.*

Sum the count and order contributions over the finite configurations. The tree version weights each configuration by its deletion multiplicity and the connected-set version weights each configuration once.

**Theorem 1.3 (Exact induced moments).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Summation.induced_exact_moments`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Summation.induced_exact_moments` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Stijn Cambie; Jorik Jooken; Stephan Wagner (2026). *On the extrema of the mean subtree order of graphs*. DOI: [10.48550/arXiv.2508.20593](https://doi.org/10.48550/arXiv.2508.20593). URL: <https://arxiv.org/abs/2508.20593v2>.

*Commentary.*

The count and total order of the actual connected induced vertex supports are 10,425,438,990,512 and 43,855,001,336,852,520.

**Theorem 1.4 (Exact tree moments).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Summation.tree_exact_moments`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Summation.tree_exact_moments` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Stijn Cambie; Jorik Jooken; Stephan Wagner (2026). *On the extrema of the mean subtree order of graphs*. DOI: [10.48550/arXiv.2508.20593](https://doi.org/10.48550/arXiv.2508.20593). URL: <https://arxiv.org/abs/2508.20593v2>.

*Commentary.*

The count and total order of the actual tree subgraphs are 14,578,492,765,509 and 61,323,620,645,707,018.

**Theorem 1.5 (The exact rational gap).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Summation.exactGap`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Summation.exactGap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Stijn Cambie; Jorik Jooken; Stephan Wagner (2026). *On the extrema of the mean subtree order of graphs*. DOI: [10.48550/arXiv.2508.20593](https://doi.org/10.48550/arXiv.2508.20593). URL: <https://arxiv.org/abs/2508.20593v2>.

*Commentary.*

The connected-set mean minus the subtree mean is exactly 1769250196421378505239933 divided by 18998398362554330511481326.

**Theorem 1.6 (Strict comparison on the witness).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Summation.strictComparison`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Summation.strictComparison` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Stijn Cambie; Jorik Jooken; Stephan Wagner (2026). *On the extrema of the mean subtree order of graphs*. DOI: [10.48550/arXiv.2508.20593](https://doi.org/10.48550/arXiv.2508.20593). URL: <https://arxiv.org/abs/2508.20593v2>.

*Commentary.*

The mean order of actual tree subgraphs is strictly smaller than the mean order of connected vertex supports.

**Theorem 1.7 (Question 1.9 is false).**

Lean statement: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Summation.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Summation.result` (`✓ std3`). ∎

*Resolves.* `Problems/cambie-jooken-wagner-mean-order-comparison` (refuted) by `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Summation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"cambie-jooken-wagner-mean-order-comparison","declaration_gid":"D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Summation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Stijn Cambie; Jorik Jooken; Stephan Wagner (2026). *On the extrema of the mean subtree order of graphs*. DOI: [10.48550/arXiv.2508.20593](https://doi.org/10.48550/arXiv.2508.20593). URL: <https://arxiv.org/abs/2508.20593v2>.

*Commentary.*

The fixed connected graph has subtree mean strictly below its connected-set mean, refuting the universal comparison.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Summation.CountOrder`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Summation.codeMoments`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Summation.exactGap`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Summation.induced_exact_moments`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Summation.result`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Summation.strictComparison`
- Truth anchor: `D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Summation.tree_exact_moments`
- Dependency: [D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Moments](CambieQ19Moments.md)
- Dependency: [D5/S3/Combinatorics/Graph/ZeroForcing/CycleConnectedForcing](../ZeroForcing/CycleConnectedForcing.md)
