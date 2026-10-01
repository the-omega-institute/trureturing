# Children of Weak Ascent Sequences

## Abstract

Appending a letter to a 210-avoiding weak ascent sequence follows the semi-Baxter succession rule.

**Definition 1.1 (The sequence label).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscentChildren.weakLabel`

*Formalization.* `D5/S3/Combinatorics/WeakAscent/WeakAscentChildren.weakLabel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Beáta Bényi, Toufik Mansour, José L. Ramírez (2024). *Pattern Avoidance in Weak Ascent Sequences*. DOI: [10.46298/dmtcs.12273](https://doi.org/10.46298/dmtcs.12273). URL: <https://arxiv.org/abs/2309.06518v4>.

*Commentary.*

Put M equal to the maximum entry, D equal to the largest inversion bottom, and H equal to one plus the number of weak ascents. The label is (M - D + 1, H - M) when the last entry equals M, and (M - D, H - M + 1) otherwise; maxima and the last entry of the empty sequence are taken as zero.

**Definition 1.2 (The semi-Baxter succession rule).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscentChildren.childLabel`

*Formalization.* `D5/S3/Combinatorics/WeakAscent/WeakAscentChildren.childLabel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Beáta Bényi, Toufik Mansour, José L. Ramírez (2024). *Pattern Avoidance in Weak Ascent Sequences*. DOI: [10.46298/dmtcs.12273](https://doi.org/10.46298/dmtcs.12273). URL: <https://arxiv.org/abs/2309.06518v4>.

*Commentary.*

A label (h, k) has children (i + 1, k + 1) for i from zero through h minus one, and (h + k - j, j + 1) for j from zero through k minus one.

**Theorem 1.3 (Labels after appending a letter).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscentChildren.weak_children_rule`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WeakAscent/WeakAscentChildren.weak_children_rule` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Beáta Bényi, Toufik Mansour, José L. Ramírez (2024). *Pattern Avoidance in Weak Ascent Sequences*. DOI: [10.46298/dmtcs.12273](https://doi.org/10.46298/dmtcs.12273). URL: <https://arxiv.org/abs/2309.06518v4>.

*Commentary.*

For every nonempty 210-avoiding weak ascent sequence with label (h, k), both coordinates are positive. The letters from its largest inversion bottom through one plus its weak ascent count are in bijection with the two index ranges of the semi-Baxter succession rule, and appending each letter gives the corresponding child label.

## References

- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscentChildren.childLabel`
- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscentChildren.weakLabel`
- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscentChildren.weak_children_rule`
- Dependency: [D5/S3/Combinatorics/WeakAscent/WeakAscentStates](WeakAscentStates.md)
