# Exact inversion increments

## Abstract

Exact inversion increments.

**Definition 1.1 (Increasing-position pair count).**

Lean statement: `D5/S3/Combinatorics/Permutation/Verkama62Count.inversions`

*Formalization.* `D5/S3/Combinatorics/Permutation/Verkama62Count.inversions` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Emil Verkama (2026). *Permutation patterns and higher connectivity in inversion graphs*. DOI: [10.48550/arXiv.2611.17237](https://doi.org/10.48550/arXiv.2611.17237). URL: <https://arxiv.org/html/2611.17237v1>.

*Commentary.*

For pi and S, sum over ordered pairs i,j in S the indicator of i < j and pi(j) < pi(i). Each unordered inversion edge contributes exactly once.

**Theorem 1.2 (Singleton increment).**

Lean statement: `D5/S3/Combinatorics/Permutation/Verkama62Count.inversions_insert`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/Verkama62Count.inversions_insert` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Emil Verkama (2026). *Permutation patterns and higher connectivity in inversion graphs*. DOI: [10.48550/arXiv.2611.17237](https://doi.org/10.48550/arXiv.2611.17237). URL: <https://arxiv.org/html/2611.17237v1>.

*Commentary.*

For x outside S, the inversion count of S union {x} equals the old inversion count plus the number of old inversion neighbours of x. The two possible orientations partition those neighbours.

**Theorem 1.3 (Double-ear increment).**

Lean statement: `D5/S3/Combinatorics/Permutation/Verkama62Count.inversion_increment`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/Verkama62Count.inversion_increment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Emil Verkama (2026). *Permutation patterns and higher connectivity in inversion graphs*. DOI: [10.48550/arXiv.2611.17237](https://doi.org/10.48550/arXiv.2611.17237). URL: <https://arxiv.org/html/2611.17237v1>.

*Commentary.*

A northeast double ear adds exactly three inversions: v has the unique old neighbour y, and u has neighbours x and v when added second. The total increment is three, independent of the size of S.

## References

- Truth anchor: `D5/S3/Combinatorics/Permutation/Verkama62Count.inversion_increment`
- Truth anchor: `D5/S3/Combinatorics/Permutation/Verkama62Count.inversions`
- Truth anchor: `D5/S3/Combinatorics/Permutation/Verkama62Count.inversions_insert`
- Dependency: [D5/S3/Combinatorics/Permutation/Verkama62Persistence](Verkama62Persistence.md)
