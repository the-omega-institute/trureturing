# Golden Gaps

## Abstract

Sorted golden name values keep exactly two adjacent gap lengths from level two.

The frozen Fibonacci-interval equivalence enumerates every level-Q golden name value in strictly increasing order. Consecutive differences of this enumeration are the tower's refinement gaps.

**Definition 1.1 (Indexed golden name value).**

Lean statement: `D5/S0/Tower/GoldenGaps.indexedNameValue`

*Formalization.* `D5/S0/Tower/GoldenGaps.indexedNameValue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The nth name value under the frozen Fibonacci-interval equivalence, reusing the GoldenNames vocabulary as its single truth source.

**Theorem 1.2 (Indexed name values increase strictly).**

$$\forall Q \in N,\; \operatorname{StrictMono}\left(\operatorname{indexedNameValue}\left(Q\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/GoldenGaps.indexed_nameValue_strictMono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The enumeration lists name values in strictly increasing order, so adjacent differences are the geometric gaps of the level.

**Theorem 1.3 (Consecutive gaps take two golden powers).**

$$\forall Q \in N,\; \operatorname{memberOf}\left(\operatorname{gap}\left(Q, i\right), \operatorname{pairSet}\left(\operatorname{goldenPow}\left(0 - Q\right), \operatorname{goldenPow}\left(0 - \left(Q + 1\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/GoldenGaps.consecutive_nameValue_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every consecutive difference at level Q equals the golden ratio to the power minus Q or to the power minus Q minus one, by the two-branch structure of the Zeckendorf tail.

**Theorem 1.4 (Adjacent gap spectrum is exactly two values).**

$$\forall Q \in N,\; \operatorname{adjacentGapSpectrum}\left(Q\right) = \operatorname{pairSet}\left(\operatorname{goldenPow}\left(0 - Q\right), \operatorname{goldenPow}\left(0 - \left(Q + 1\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/GoldenGaps.adjacent_gap_spectrum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

From level two onward both gap lengths occur, so the adjacent-gap spectrum is exactly the two-element set of those golden powers; normalizing by the larger gap gives the two-type spectrum one and inverse golden ratio. Levels zero and one are degenerate with at most one gap, which is why the exact form assumes level at least two.

## References

- Truth anchor: `D5/S0/Tower/GoldenGaps.adjacent_gap_spectrum`
- Truth anchor: `D5/S0/Tower/GoldenGaps.consecutive_nameValue_gap`
- Truth anchor: `D5/S0/Tower/GoldenGaps.indexedNameValue`
- Truth anchor: `D5/S0/Tower/GoldenGaps.indexed_nameValue_strictMono`
- Dependency: [D5/S0/Tower/GoldenNames](GoldenNames.md)
