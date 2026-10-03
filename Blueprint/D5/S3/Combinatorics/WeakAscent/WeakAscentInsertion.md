# Inserting a New Maximum

## Abstract

Insertion and deletion of a largest letter characterize avoidance of 2-41-3.

**Theorem 1.1 (Deletion of the inserted maximum).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscentInsertion.delete_maximum_avoids`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WeakAscent/WeakAscentInsertion.delete_maximum_avoids` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Beáta Bényi, Toufik Mansour, José L. Ramírez (2024). *Pattern Avoidance in Weak Ascent Sequences*. DOI: [10.46298/dmtcs.12273](https://doi.org/10.46298/dmtcs.12273). URL: <https://arxiv.org/abs/2309.06518v4>.

*Commentary.*

Let a new letter exceed every entry of a word p, and insert it at any position from zero through the length of p. If the resulting word avoids 2-41-3, then p also avoids 2-41-3.

**Theorem 1.2 (The insertion criterion).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscentInsertion.active_site_criterion`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WeakAscent/WeakAscentInsertion.active_site_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Beáta Bényi, Toufik Mansour, José L. Ramírez (2024). *Pattern Avoidance in Weak Ascent Sequences*. DOI: [10.46298/dmtcs.12273](https://doi.org/10.46298/dmtcs.12273). URL: <https://arxiv.org/abs/2309.06518v4>.

*Commentary.*

Let p avoid 2-41-3, let s be a position from zero through its length, and let a new letter exceed every entry of p. Inserting this letter at s preserves avoidance exactly when there are no positions i and k with i less than s less than k less than the length of p such that the entry at s is less than the entry at i and the entry at i is less than the entry at k. Positions are numbered from zero.

## References

- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscentInsertion.active_site_criterion`
- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscentInsertion.delete_maximum_avoids`
- Dependency: [D5/S3/Combinatorics/WeakAscent/WeakAscentChildren](WeakAscentChildren.md)
