# A singleton between double ears

## Abstract

A singleton between double ears.

**Definition 1.1 (Old inversion neighbours).**

Lean statement: `D5/S3/Combinatorics/Permutation/Verkama62Persistence.neighbours`

*Formalization.* `D5/S3/Combinatorics/Permutation/Verkama62Persistence.neighbours` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Emil Verkama (2026). *Permutation patterns and higher connectivity in inversion graphs*. DOI: [10.48550/arXiv.2611.17237](https://doi.org/10.48550/arXiv.2611.17237). URL: <https://arxiv.org/html/2611.17237v1>.

*Commentary.*

For a new position x, the old neighbours are precisely the i in S with i < x and pi(x) < pi(i), or x < i and pi(i) < pi(x).

**Theorem 1.2 (Persistence through one degree-two singleton).**

Lean statement: `D5/S3/Combinatorics/Permutation/Verkama62Persistence.singleton_terminal`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/Verkama62Persistence.singleton_terminal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Emil Verkama (2026). *Permutation patterns and higher connectivity in inversion graphs*. DOI: [10.48550/arXiv.2611.17237](https://doi.org/10.48550/arXiv.2611.17237). URL: <https://arxiv.org/html/2611.17237v1>.

*Commentary.*

For every finite permutation and fresh state S, inserting a position x outside S with exactly two old inversion neighbours leaves a terminal 3412. If x becomes the new maximum, it lies between b and c. If it becomes rightmost, its value lies between pi(d) and pi(a). If it changes neither extremum, the original terminal pattern remains.

**Theorem 1.3 (Cheap transitions cannot precede a double ear).**

Lean statement: `D5/S3/Combinatorics/Permutation/Verkama62Persistence.no_cheap_double`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/Verkama62Persistence.no_cheap_double` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Emil Verkama (2026). *Permutation patterns and higher connectivity in inversion graphs*. DOI: [10.48550/arXiv.2611.17237](https://doi.org/10.48550/arXiv.2611.17237). URL: <https://arxiv.org/html/2611.17237v1>.

*Commentary.*

In a 351624-avoiding permutation, a fresh state admits no northeast double ear. The same holds after inserting exactly one singleton having two old neighbours. No assertion of persistence through arbitrary longer sequences is needed.

## References

- Truth anchor: `D5/S3/Combinatorics/Permutation/Verkama62Persistence.neighbours`
- Truth anchor: `D5/S3/Combinatorics/Permutation/Verkama62Persistence.no_cheap_double`
- Truth anchor: `D5/S3/Combinatorics/Permutation/Verkama62Persistence.singleton_terminal`
- Dependency: [D5/S3/Combinatorics/Permutation/Verkama62Local](Verkama62Local.md)
