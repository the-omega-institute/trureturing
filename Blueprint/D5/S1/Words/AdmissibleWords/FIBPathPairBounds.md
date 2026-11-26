# Sharp path occupancy bounds from a fixed start

## Abstract

Cumulative downward variation bounds the oriented difference between two sites.

**Definition 1.1 (Downward variation between two sites).**

Lean statement: `D5/S1/Words/AdmissibleWords/FIBPathPairBounds.downwardVariation`

*Formalization.* `D5/S1/Words/AdmissibleWords/FIBPathPairBounds.downwardVariation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Starting at the chosen site, add the positive part of each successive decrease in the transformed profile up to the target site.

**Theorem 1.2 (The sharp event difference).**

Lean statement: `D5/S1/Words/AdmissibleWords/FIBPathPairBounds.sharp_hard_core_difference`

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/FIBPathPairBounds.sharp_hard_core_difference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Prescribe nonnegative occupancies with adjacent sums at most one, which also bounds each occupancy by one. Consider measurable events in the half-open unit interval with the prescribed occupancies and pointwise disjoint adjacent events. Complement the odd-indexed events within that interval and complement their marginals. For any target at or after a fixed source, the mass in the transformed source event outside the transformed target event is at most the least of the source mass, the complement of the target mass, and the downward variation between them. One family of measurable occupation events attains the bound for every such target. Divide the unit interval at the transformed source mass. In each part use an initial interval. Choose the first length as the maximum of zero, the source plus target mass minus one, and the source mass minus the downward variation. Before the source use the lesser of the two masses. The second length supplies the rest of the prescribed mass. Both lengths follow the direction of each adjacent change, giving nested transformed events and disjoint adjacent occupied events.

**Theorem 1.3 (One law on admissible finite words).**

Lean statement: `D5/S1/Words/AdmissibleWords/FIBPathPairBounds.word_attainment`

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/FIBPathPairBounds.word_attainment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite profile whose occupancies lie between zero and one and whose adjacent sums are at most one, the indicator of each occupied event yields a word with no adjacent ones. The site measures are the prescribed occupancies, and each occupancy event is measurable and contained in the half-open unit interval. The oriented differences within the interval after alternating complementation reach their bounds simultaneously from the chosen source to all later targets.

## References

- Truth anchor: `D5/S1/Words/AdmissibleWords/FIBPathPairBounds.downwardVariation`
- Truth anchor: `D5/S1/Words/AdmissibleWords/FIBPathPairBounds.sharp_hard_core_difference`
- Truth anchor: `D5/S1/Words/AdmissibleWords/FIBPathPairBounds.word_attainment`
- Dependency: [D5/S1/Words/AdmissibleWords/AdmissibleCount](AdmissibleCount.md)
- Dependency: [D5/S1/Words/AdmissibleWords/SourceOverlapCoupling](SourceOverlapCoupling.md)
