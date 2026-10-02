# Children of Vincular-Avoiding Permutations

## Abstract

Permutations avoiding 2-41-3 have the semi-Baxter succession rule.

**Definition 1.1 (The permutation label).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscentPermChildren.permLabel`

*Formalization.* `D5/S3/Combinatorics/WeakAscent/WeakAscentPermChildren.permLabel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Beáta Bényi, Toufik Mansour, José L. Ramírez (2024). *Pattern Avoidance in Weak Ascent Sequences*. DOI: [10.46298/dmtcs.12273](https://doi.org/10.46298/dmtcs.12273). URL: <https://arxiv.org/abs/2309.06518v4>.

*Commentary.*

For a permutation p of one through n, its label (h, k) has h equal to the number of active insertion sites strictly after the position of n and k equal to the number of positions whose entries exceed all earlier entries. Positions and insertion sites are numbered from zero.

**Theorem 1.2 (Labels after inserting the maximum).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscentPermChildren.permutation_children_rule`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WeakAscent/WeakAscentPermChildren.permutation_children_rule` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Beáta Bényi, Toufik Mansour, José L. Ramírez (2024). *Pattern Avoidance in Weak Ascent Sequences*. DOI: [10.46298/dmtcs.12273](https://doi.org/10.46298/dmtcs.12273). URL: <https://arxiv.org/abs/2309.06518v4>.

*Commentary.*

For every nonempty permutation of one through n avoiding 2-41-3 with label (h, k), both coordinates are positive. The permutations obtained by inserting n + 1 at an active site are in bijection with the two index ranges of the semi-Baxter succession rule, and each resulting permutation has the corresponding child label.

## References

- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscentPermChildren.permLabel`
- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscentPermChildren.permutation_children_rule`
- Dependency: [D5/S3/Combinatorics/WeakAscent/WeakAscentSites](WeakAscentSites.md)
