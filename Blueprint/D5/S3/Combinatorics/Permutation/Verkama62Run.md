# Deletion connectivity of northeast ear runs

## Abstract

Deletion connectivity of northeast ear runs.

**Theorem 1.1 (Deletion connectivity).**

Lean statement: `D5/S3/Combinatorics/Permutation/Verkama62Run.robust`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/Verkama62Run.robust` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Emil Verkama (2026). *Permutation patterns and higher connectivity in inversion graphs*. DOI: [10.48550/arXiv.2611.17237](https://doi.org/10.48550/arXiv.2611.17237). URL: <https://arxiv.org/html/2611.17237v1>.

*Commentary.*

For every permutation pi, finite set S, and permitted ear run on S, deleting any ambient point w leaves the induced value graph on pi(S minus {w}) connected. A triangle and a 3412 square have this property. Inserting a singleton with at least two old neighbours leaves an attachment after any deletion. A double ear has distinct old attachments and an edge between its two new vertices; after any one deletion its surviving new vertices connect to the surviving old stage.

## References

- Truth anchor: `D5/S3/Combinatorics/Permutation/Verkama62Run.robust`
- Dependency: [D5/S3/Combinatorics/Permutation/Verkama62EarGeometry](Verkama62EarGeometry.md)
