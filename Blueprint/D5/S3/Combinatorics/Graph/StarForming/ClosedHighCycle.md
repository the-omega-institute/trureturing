# Closing the high cycle removes the two-hub exception

## Abstract

Closing the high cycle removes the two-hub exception

The zero-hub score is bounded by the three cell caps. In the two-hub case the intact final high edge excludes the size-thirteen pattern. Actual graph extraction is supplied separately by ClosedCore.

**Theorem 1.1 (zero hub score).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/ClosedHighCycle.zero_hub_score`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/ClosedHighCycle.zero_hub_score` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem zero_hub_score (first middle last : Cell) (hfirst : Valid first 0 0) (hmiddle : Valid middle 0 0) (hlast : Valid last 0 0) : 3 + first.weight + middle.weight + last.weight ≤ 12.

**Theorem 1.2 (closed two hub score).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/ClosedHighCycle.closed_two_hub_score`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/ClosedHighCycle.closed_two_hub_score` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem closed_two_hub_score (first middle last : Cell) (hfirst : Valid first 1 1) (hmiddle : Valid middle 1 1) (hlast : Valid last 1 1) (hfirstAcross : Across first middle) (hlastAcross : Across middle last) (hclosedHigh : last.highRight + first.highLeft + first.highRight ≤ 2) : 3 + first.weight + middle.weight + last.weight + 2 ≤ 12.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/ClosedHighCycle.closed_two_hub_score`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/ClosedHighCycle.zero_hub_score`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/LongCoreUpper](LongCoreUpper.md)
