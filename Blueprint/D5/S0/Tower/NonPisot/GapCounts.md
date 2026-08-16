# Measured Non-Pisot Gap Counts

## Abstract

The measured normalized gap spectra for beta13 have cardinalities six, eight, and ten at levels six, eight, and ten, while the frozen Tribonacci count is three.

Names are finite greedy beta-shift words over digits zero, one, and two. Every suffix is compared with the certified greedy expansion prefix. The names remain in lexicographic order, their values are normalized by the common positive factor beta13^Q, and only internal adjacent differences are placed in the finite spectrum.

Exact pairs (a,b) represent a+b beta13. The three finite computations agree with the certified greedy-remainder spectra, and irrationality makes the passage from pair codes to real gap values injective.

**Theorem 1.1 (Six normalized gap types at level six).**

$$\operatorname{card}\left(\operatorname{beta13NormalizedGapSpectrum}\left(6\right)\right) = 6$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/NonPisot/GapCounts.beta13_normalized_gap_type_count_six` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite internal adjacent-gap spectrum at Q = 6 has cardinality six.

**Theorem 1.2 (Eight normalized gap types at level eight).**

$$\operatorname{card}\left(\operatorname{beta13NormalizedGapSpectrum}\left(8\right)\right) = 8$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/NonPisot/GapCounts.beta13_normalized_gap_type_count_eight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite internal adjacent-gap spectrum at Q = 8 has cardinality eight.

**Theorem 1.3 (Ten normalized gap types at level ten).**

$$\operatorname{card}\left(\operatorname{beta13NormalizedGapSpectrum}\left(10\right)\right) = 10$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/NonPisot/GapCounts.beta13_normalized_gap_type_count_ten` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite internal adjacent-gap spectrum at Q = 10 has cardinality ten.

**Theorem 1.4 (The frozen Tribonacci count is three).**

$$\forall Q \in N,\; Q \ge 3 \Rightarrow \operatorname{card}\left(\operatorname{tribonacciAdjacentGapSpectrum}\left(Q\right)\right) = 3$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/NonPisot/GapCounts.tribonacci_normalized_gap_type_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is a fully qualified wrapper around the frozen Tribonacci adjacent-gap-spectrum cardinality theorem. Common positive normalization does not alter the number of gap types.

## References

- Truth anchor: `D5/S0/Tower/NonPisot/GapCounts.beta13_normalized_gap_type_count_eight`
- Truth anchor: `D5/S0/Tower/NonPisot/GapCounts.beta13_normalized_gap_type_count_six`
- Truth anchor: `D5/S0/Tower/NonPisot/GapCounts.beta13_normalized_gap_type_count_ten`
- Truth anchor: `D5/S0/Tower/NonPisot/GapCounts.tribonacci_normalized_gap_type_count`
- Dependency: [D5/S0/Tower/NonPisot/Beta13](Beta13.md)
- Dependency: [D5/S0/Tower/Tribonacci/Gaps](../Tribonacci/Gaps.md)
