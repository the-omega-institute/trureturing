# An integer potential for avoiding ear runs

## Abstract

An integer potential for avoiding ear runs.

**Definition 1.1 (Northeast ear runs).**

Lean statement: `D5/S3/Combinatorics/Permutation/Verkama62Charge.EarRun`

*Formalization.* `D5/S3/Combinatorics/Permutation/Verkama62Charge.EarRun` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Emil Verkama (2026). *Permutation patterns and higher connectivity in inversion graphs*. DOI: [10.48550/arXiv.2611.17237](https://doi.org/10.48550/arXiv.2611.17237). URL: <https://arxiv.org/html/2611.17237v1>.

*Commentary.*

A run starts with three decreasing points or four points of relative order 3412. Each step inserts a singleton outside the old set with at least two old neighbours, or a northeast double ear. This definition specifies a class of runs; it does not assert that a graph has such a run.

**Definition 1.2 (Signed potential).**

Lean statement: `D5/S3/Combinatorics/Permutation/Verkama62Charge.potential`

*Formalization.* `D5/S3/Combinatorics/Permutation/Verkama62Charge.potential` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Emil Verkama (2026). *Permutation patterns and higher connectivity in inversion graphs*. DOI: [10.48550/arXiv.2611.17237](https://doi.org/10.48550/arXiv.2611.17237). URL: <https://arxiv.org/html/2611.17237v1>.

*Commentary.*

The integer potential is 7 times the cardinality of S minus 4 times its inversion count. A singleton of old degree d changes it by 7 - 4d, and a double ear increases it by two. All subtraction takes place in the integers.

**Theorem 1.3 (The bound for every avoiding run).**

Lean statement: `D5/S3/Combinatorics/Permutation/Verkama62Charge.ear_run_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/Verkama62Charge.ear_run_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Emil Verkama (2026). *Permutation patterns and higher connectivity in inversion graphs*. DOI: [10.48550/arXiv.2611.17237](https://doi.org/10.48550/arXiv.2611.17237). URL: <https://arxiv.org/html/2611.17237v1>.

*Commentary.*

For every n, permutation pi of Fin n and finite set S, an ear run ending at S and classical 351624-avoidance imply 7|S| <= 4 inv(S) + 12. The induction maintains three alternatives: potential at most 10; potential at most 11 with a terminal pattern; or potential at most 12 with a fresh pattern. A triangle starts at potential 9, and a square starts fresh at potential 12. Terminal states exclude the next double ear; a degree-two singleton lowers the potential by one and preserves a terminal pattern from a fresh state. A higher-degree singleton lowers it by at least five.

## References

- Truth anchor: `D5/S3/Combinatorics/Permutation/Verkama62Charge.EarRun`
- Truth anchor: `D5/S3/Combinatorics/Permutation/Verkama62Charge.ear_run_bound`
- Truth anchor: `D5/S3/Combinatorics/Permutation/Verkama62Charge.potential`
- Dependency: [D5/S3/Combinatorics/Permutation/Verkama62Count](Verkama62Count.md)
