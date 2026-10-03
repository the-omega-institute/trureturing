# The Archer-Bourne square recurrence fails at eleven

## Abstract

There are nine indecomposable permutations of length eleven avoiding 312 and 54321 whose squares avoid 132, which refutes the Archer-Bourne recurrence conjecture.

**Definition 1.1 (Candidates obtained by inserting successive maxima).**

Lean statement: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareRefutation.componentCandidates`

*Formalization.* `D5/S3/Combinatorics/PermutationSquare/PermutationSquareRefutation.componentCandidates` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Noel Bourne (2026). *Pattern avoidance in compositions and powers of permutations*. DOI: [10.46298/dmtcs.17199](https://doi.org/10.46298/dmtcs.17199). URL: <https://arxiv.org/abs/2505.05218v3>.

*Commentary.*

At parameter zero the candidate list contains only the permutation consisting of one. To obtain the candidates at parameter size plus one, take each candidate at parameter size and insert size plus two immediately before a decreasing suffix of length one, two or three. A suffix length is permitted only when it does not exceed the length of the candidate and the suffix is strictly decreasing. Candidates at parameter size have length size plus one.

**Theorem 1.2 (Completeness of maximum insertion).**

Lean statement: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareRefutation.component_candidates_complete`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PermutationSquare/PermutationSquareRefutation.component_candidates_complete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Noel Bourne (2026). *Pattern avoidance in compositions and powers of permutations*. DOI: [10.46298/dmtcs.17199](https://doi.org/10.46298/dmtcs.17199). URL: <https://arxiv.org/abs/2505.05218v3>.

*Commentary.*

For every nonnegative size, every permutation of one through size plus one that ends in one and avoids 312 and 54321 occurs in the candidate list at parameter size. Removing its maximum leaves a permutation with the same conditions; the entries following that maximum form a nonempty decreasing suffix of length at most three.

**Theorem 1.3 (Refutation at length eleven).**

Lean statement: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareRefutation.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PermutationSquare/PermutationSquareRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/archer-bourne-square-tetranacci-refutation` (refuted) by `D5/S3/Combinatorics/PermutationSquare/PermutationSquareRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"archer-bourne-square-tetranacci-refutation","declaration_gid":"D5/S3/Combinatorics/PermutationSquare/PermutationSquareRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Noel Bourne (2026). *Pattern avoidance in compositions and powers of permutations*. DOI: [10.46298/dmtcs.17199](https://doi.org/10.46298/dmtcs.17199). URL: <https://arxiv.org/abs/2505.05218v3>.

*Commentary.*

The Archer-Bourne conjecture that a(n) equals the sum of the four preceding terms plus n minus one for every n at least six is false. At length eleven, the number of indecomposable permutations avoiding 312 and 54321 whose squares avoid 132 is nine. The corrected recurrence therefore gives a(11) equal to a(10) plus a(9) plus a(8) plus a(7) plus nine, whereas the conjectured recurrence requires the same four terms plus ten.

## References

- Truth anchor: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareRefutation.componentCandidates`
- Truth anchor: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareRefutation.component_candidates_complete`
- Truth anchor: `D5/S3/Combinatorics/PermutationSquare/PermutationSquareRefutation.result`
- Dependency: [D5/S3/Combinatorics/PermutationSquare/PermutationSquareCounting](PermutationSquareCounting.md)
