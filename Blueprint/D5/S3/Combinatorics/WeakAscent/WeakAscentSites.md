# Active Sites and Records

## Abstract

Record positions determine how active insertion sites change after inserting a new maximum.

**Definition 1.1 (Active insertion sites).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscentSites.activeSites`

*Formalization.* `D5/S3/Combinatorics/WeakAscent/WeakAscentSites.activeSites` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Beáta Bényi, Toufik Mansour, José L. Ramírez (2024). *Pattern Avoidance in Weak Ascent Sequences*. DOI: [10.46298/dmtcs.12273](https://doi.org/10.46298/dmtcs.12273). URL: <https://arxiv.org/abs/2309.06518v4>.

*Commentary.*

For a word p of length n, the active sites are the positions from zero through n at which inserting n + 1 gives a word avoiding 2-41-3.

**Definition 1.2 (Record positions).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscentSites.recordSites`

*Formalization.* `D5/S3/Combinatorics/WeakAscent/WeakAscentSites.recordSites` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Beáta Bényi, Toufik Mansour, José L. Ramírez (2024). *Pattern Avoidance in Weak Ascent Sequences*. DOI: [10.46298/dmtcs.12273](https://doi.org/10.46298/dmtcs.12273). URL: <https://arxiv.org/abs/2309.06518v4>.

*Commentary.*

The record positions of a word are the positions whose entries are strictly greater than every entry at an earlier position. Positions are numbered from zero.

**Theorem 1.3 (Active sites up to the maximum).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscentSites.active_record_structure`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WeakAscent/WeakAscentSites.active_record_structure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Beáta Bényi, Toufik Mansour, José L. Ramírez (2024). *Pattern Avoidance in Weak Ascent Sequences*. DOI: [10.46298/dmtcs.12273](https://doi.org/10.46298/dmtcs.12273). URL: <https://arxiv.org/abs/2309.06518v4>.

*Commentary.*

In every nonempty permutation of one through n avoiding 2-41-3, the active sites at or before the position of n are exactly the record positions, every record position is at or before the position of n, and the two end sites zero and n are active.

**Theorem 1.4 (Active sites after insertion).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscentSites.active_sites_insert`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WeakAscent/WeakAscentSites.active_sites_insert` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Beáta Bényi, Toufik Mansour, José L. Ramírez (2024). *Pattern Avoidance in Weak Ascent Sequences*. DOI: [10.46298/dmtcs.12273](https://doi.org/10.46298/dmtcs.12273). URL: <https://arxiv.org/abs/2309.06518v4>.

*Commentary.*

Let p be a permutation of one through n avoiding 2-41-3, and insert n + 1 at an active site s. The active sites of the resulting permutation are exactly the record positions of p strictly less than s, the sites s and s + 1, and the sites obtained by adding one to each active site of p strictly greater than s.

## References

- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscentSites.activeSites`
- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscentSites.active_record_structure`
- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscentSites.active_sites_insert`
- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscentSites.recordSites`
- Dependency: [D5/S3/Combinatorics/WeakAscent/WeakAscentInsertion](WeakAscentInsertion.md)
