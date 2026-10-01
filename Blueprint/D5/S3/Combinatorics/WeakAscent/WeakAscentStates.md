# States of 210-Avoiding Weak Ascent Sequences

## Abstract

The maximum, inversion bottom and weak ascent count control appending a letter.

**Definition 1.1 (The largest inversion bottom).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscentStates.inversionBottom`

*Formalization.* `D5/S3/Combinatorics/WeakAscent/WeakAscentStates.inversionBottom` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Beáta Bényi, Toufik Mansour, José L. Ramírez (2024). *Pattern Avoidance in Weak Ascent Sequences*. DOI: [10.46298/dmtcs.12273](https://doi.org/10.46298/dmtcs.12273). URL: <https://arxiv.org/abs/2309.06518v4>.

*Commentary.*

The largest inversion bottom of a sequence is the greatest entry that is strictly smaller than an entry at an earlier position, or zero if there is no such entry.

**Theorem 1.2 (The last entry is an extreme).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscentStates.last_extreme`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WeakAscent/WeakAscentStates.last_extreme` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Beáta Bényi, Toufik Mansour, José L. Ramírez (2024). *Pattern Avoidance in Weak Ascent Sequences*. DOI: [10.46298/dmtcs.12273](https://doi.org/10.46298/dmtcs.12273). URL: <https://arxiv.org/abs/2309.06518v4>.

*Commentary.*

For every nonempty sequence avoiding 210, the largest inversion bottom D is at most both the maximum M and the last entry. The last entry either equals M, or equals D with D strictly less than M.

**Theorem 1.3 (The interval of appendable letters).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscentStates.append_interval`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WeakAscent/WeakAscentStates.append_interval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Beáta Bényi, Toufik Mansour, José L. Ramírez (2024). *Pattern Avoidance in Weak Ascent Sequences*. DOI: [10.46298/dmtcs.12273](https://doi.org/10.46298/dmtcs.12273). URL: <https://arxiv.org/abs/2309.06518v4>.

*Commentary.*

For every nonempty 210-avoiding weak ascent sequence, appending a nonnegative letter x gives another 210-avoiding weak ascent sequence exactly when x is at least the largest inversion bottom and at most one plus the weak ascent count.

**Theorem 1.4 (State changes under appending).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscentStates.append_state`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WeakAscent/WeakAscentStates.append_state` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Beáta Bényi, Toufik Mansour, José L. Ramírez (2024). *Pattern Avoidance in Weak Ascent Sequences*. DOI: [10.46298/dmtcs.12273](https://doi.org/10.46298/dmtcs.12273). URL: <https://arxiv.org/abs/2309.06518v4>.

*Commentary.*

For any sequence with maximum M and largest inversion bottom D, appending x changes the maximum to the greater of M and x. The weak ascent count increases by one precisely when the sequence is nonempty and its last entry is at most x. The new largest inversion bottom is the greater of D and x if x is less than M, and is D otherwise; the maximum of the empty sequence is zero.

## References

- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscentStates.append_interval`
- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscentStates.append_state`
- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscentStates.inversionBottom`
- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscentStates.last_extreme`
- Dependency: [D5/S3/Combinatorics/WeakAscent/WeakAscentGrowth](WeakAscentGrowth.md)
