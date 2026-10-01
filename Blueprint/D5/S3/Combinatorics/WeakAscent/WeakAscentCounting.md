# Counting Weak Ascent Extensions

## Abstract

The semi-Baxter succession rule counts extensions of 210-avoiding weak ascent sequences.

**Definition 1.1 (Descendants in the labelled tree).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscentCounting.treeCount`

*Formalization.* `D5/S3/Combinatorics/WeakAscent/WeakAscentCounting.treeCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Beáta Bényi, Toufik Mansour, José L. Ramírez (2024). *Pattern Avoidance in Weak Ascent Sequences*. DOI: [10.46298/dmtcs.12273](https://doi.org/10.46298/dmtcs.12273). URL: <https://arxiv.org/abs/2309.06518v4>.

*Commentary.*

The number T(d, h, k) is one at depth zero. At depth d + 1 it is the sum of T(d, a, b) over all child labels (a, b) of (h, k) in the semi-Baxter succession rule, with multiplicity given by the child indices.

**Definition 1.2 (Extensions with a prescribed prefix).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscentCounting.weakExtensions`

*Formalization.* `D5/S3/Combinatorics/WeakAscent/WeakAscentCounting.weakExtensions` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Beáta Bényi, Toufik Mansour, José L. Ramírez (2024). *Pattern Avoidance in Weak Ascent Sequences*. DOI: [10.46298/dmtcs.12273](https://doi.org/10.46298/dmtcs.12273). URL: <https://arxiv.org/abs/2309.06518v4>.

*Commentary.*

The extensions of a sequence e at depth d are the 210-avoiding weak ascent sequences of length equal to the length of e plus d whose prefix of length equal to the length of e is e.

**Theorem 1.3 (The extension count).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscentCounting.weak_extensions_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WeakAscent/WeakAscentCounting.weak_extensions_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Beáta Bényi, Toufik Mansour, José L. Ramírez (2024). *Pattern Avoidance in Weak Ascent Sequences*. DOI: [10.46298/dmtcs.12273](https://doi.org/10.46298/dmtcs.12273). URL: <https://arxiv.org/abs/2309.06518v4>.

*Commentary.*

For every nonempty 210-avoiding weak ascent sequence e with label (h, k) and every nonnegative depth d, the number of extensions of e at depth d equals T(d, h, k).

## References

- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscentCounting.treeCount`
- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscentCounting.weakExtensions`
- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscentCounting.weak_extensions_count`
- Dependency: [D5/S3/Combinatorics/WeakAscent/WeakAscentChildren](WeakAscentChildren.md)
