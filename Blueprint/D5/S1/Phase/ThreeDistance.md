# Three Distances in the Golden Rotation

## Abstract

The cyclic adjacent gaps of a finite golden-ratio rotation orbit have at most three distinct lengths.

For a natural number $N$, the finite orbit in `D5/S1/Phase/ThreeDistance` consists of the fractional parts of n times the golden ratio, for 0 <= n < N. The function goldenGapValues takes the distinct lengths of gaps between successive orbit points in increasing order, including the cyclic gap from the last point back to the first.

**Theorem 1.1 (At most three distinct cyclic gap lengths).**

$$\forall N \in \mathbb{N},\ \operatorname{card}\left(\operatorname{goldenGapValues}\left(N\right)\right) \le 3$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/ThreeDistance.three_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural N, the cardinality of goldenGapValues(N) is at most three. This counts distinct lengths, rather than the number of gaps. There is no positive-N hypothesis: the total gap construction assigns the singleton gap of length one to the empty orbit as well as to a one-point orbit.

The proof specializes the general real-rotation bound `D5/S1/Phase/ThreeGap/Main.three_gap_card_le_three` to the golden ratio. That theorem is the repository's MIT-licensed port of Dirk Kunert's formalization of the classical three-gap theorem. The present result is its repository-derived specialization; it asserts neither that all three lengths occur for every N nor a formula for their multiplicities.

## References

- Truth anchor: `D5/S1/Phase/ThreeDistance.three_gap`
- Truth anchor: `D5/S1/Phase/ThreeGap/Main.three_gap_card_le_three`
