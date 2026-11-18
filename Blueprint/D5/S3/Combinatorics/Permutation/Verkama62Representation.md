# One-based notation and the rational bound

## Abstract

One-based notation and the rational bound.

**Definition 1.1 (Printed classical avoidance).**

Lean statement: `D5/S3/Combinatorics/Permutation/Verkama62Representation.ContainsOneBased`

*Formalization.* `D5/S3/Combinatorics/Permutation/Verkama62Representation.ContainsOneBased` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Emil Verkama (2026). *Permutation patterns and higher connectivity in inversion graphs*. DOI: [10.48550/arXiv.2611.17237](https://doi.org/10.48550/arXiv.2611.17237). URL: <https://arxiv.org/html/2611.17237v1>.

*Commentary.*

An occurrence is an increasing embedding of the six positions whose relative value order equals [3,5,1,6,2,4]. The values pi(i).val + 1 represent the source labels in {1,...,n}. Subtracting one from each pattern value gives [2,4,0,5,1,3].

**Theorem 1.2 (Equality with the list inversion statistic).**

Lean statement: `D5/S3/Combinatorics/Permutation/Verkama62Representation.word_inversions`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/Verkama62Representation.word_inversions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Emil Verkama (2026). *Permutation patterns and higher connectivity in inversion graphs*. DOI: [10.48550/arXiv.2611.17237](https://doi.org/10.48550/arXiv.2611.17237). URL: <https://arxiv.org/html/2611.17237v1>.

*Commentary.*

For every finite permutation pi, the existing inversion counter of its one-based word PSW.word pi equals the increasing-position pair count on all positions. The proof identifies the range-indexed row counts and their finite sums.

**Theorem 1.3 (Exact rational comparison).**

Lean statement: `D5/S3/Combinatorics/Permutation/Verkama62Representation.rational_bound_of_ear_run`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/Verkama62Representation.rational_bound_of_ear_run` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Emil Verkama (2026). *Permutation patterns and higher connectivity in inversion graphs*. DOI: [10.48550/arXiv.2611.17237](https://doi.org/10.48550/arXiv.2611.17237). URL: <https://arxiv.org/html/2611.17237v1>.

*Commentary.*

For every n and permutation pi, one-based classical 351624-avoidance and a northeast ear run reaching all positions imply inv(pi) >= (7/4)n - 3 over the rationals. The proof uses the subtraction-free integer comparison 7n <= 4 inv(pi) + 12. Existence of the run is an explicit hypothesis.

## References

- Truth anchor: `D5/S3/Combinatorics/Permutation/Verkama62Representation.ContainsOneBased`
- Truth anchor: `D5/S3/Combinatorics/Permutation/Verkama62Representation.rational_bound_of_ear_run`
- Truth anchor: `D5/S3/Combinatorics/Permutation/Verkama62Representation.word_inversions`
- Dependency: [D5/S3/Combinatorics/IndecomposableInversion/FranklinInversionDefs](../IndecomposableInversion/FranklinInversionDefs.md)
- Dependency: [D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsWord](../Permanental/PanSkanderaWangAllSplitsWord.md)
- Dependency: [D5/S3/Combinatorics/Permutation/Verkama62Charge](Verkama62Charge.md)
