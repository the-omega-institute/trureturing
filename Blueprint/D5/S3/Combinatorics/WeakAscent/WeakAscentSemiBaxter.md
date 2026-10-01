# Equinumerosity with Semi-Baxter Permutations

## Abstract

Weak ascent sequences avoiding 210 are counted by the semi-Baxter numbers.

**Definition 1.1 (Permutation extensions).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscentSemiBaxter.permExtensions`

*Formalization.* `D5/S3/Combinatorics/WeakAscent/WeakAscentSemiBaxter.permExtensions` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Beáta Bényi, Toufik Mansour, José L. Ramírez (2024). *Pattern Avoidance in Weak Ascent Sequences*. DOI: [10.46298/dmtcs.12273](https://doi.org/10.46298/dmtcs.12273). URL: <https://arxiv.org/abs/2309.06518v4>.

*Commentary.*

The extensions of a word p at depth d are the permutations of one through the length of p plus d avoiding 2-41-3 whose restriction to entries at most the length of p equals p.

**Theorem 1.2 (The weak ascent and semi-Baxter enumeration).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscentSemiBaxter.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WeakAscent/WeakAscentSemiBaxter.result` (`✓ std3`). ∎

*Resolves.* `Problems/benyi-mansour-ramirez-weak-ascent-210` (proved) by `D5/S3/Combinatorics/WeakAscent/WeakAscentSemiBaxter.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"benyi-mansour-ramirez-weak-ascent-210","declaration_gid":"D5/S3/Combinatorics/WeakAscent/WeakAscentSemiBaxter.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Beáta Bényi, Toufik Mansour, José L. Ramírez (2024). *Pattern Avoidance in Weak Ascent Sequences*. DOI: [10.46298/dmtcs.12273](https://doi.org/10.46298/dmtcs.12273). URL: <https://arxiv.org/abs/2309.06518v4>.

*Commentary.*

For every nonnegative n, the number of 210-avoiding weak ascent sequences of length n equals the number of permutations of one through n avoiding the vincular pattern 2-41-3.

## References

- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscentSemiBaxter.permExtensions`
- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscentSemiBaxter.result`
- Dependency: [D5/S3/Combinatorics/WeakAscent/WeakAscentCounting](WeakAscentCounting.md)
- Dependency: [D5/S3/Combinatorics/WeakAscent/WeakAscentPermParents](WeakAscentPermParents.md)
