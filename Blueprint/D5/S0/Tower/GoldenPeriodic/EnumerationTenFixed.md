# Period-Ten Fixed-Point Decomposition

## Abstract

The 123 period-ten fixed-point equations decompose into eight bounded blocks.

The legal three-step prefixes LLL, LLR, LRT, RTL, RTR, TLL, TLR, and TRT partition the symbolic equations. Each block is compared separately with the inherited and primitive orbit phases.

**Theorem 1.1 (The eight fixed-point blocks are bounded).**

$$\operatorname{periodTenFixedBlockLengths}\left(\right) = \operatorname{list}\left(21, 13, 21, 21, 13, 13, 8, 13\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/GoldenPeriodic/EnumerationTenFixed.golden_fixed_point_block_counts_ten` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The block sizes are 21, 13, 21, 21, 13, 13, 8, and 13; no arithmetic comparison expands more than twenty-one equations at once.

**Theorem 1.2 (Every period-ten fixed point is an enumerated orbit phase).**

$$\operatorname{toFinset}\left(\operatorname{goldenFixedPointCodes}\left(10\right)\right) = \mathit{goldenExpectedPointCodesTen}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/GoldenPeriodic/EnumerationTenFixed.golden_fixed_point_codes_ten_decompose` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

After the eight exact comparisons are recombined, the fixed-point codes are exactly the inherited divisor-period phases and the eleven new ten-cycles.

## References

- Truth anchor: `D5/S0/Tower/GoldenPeriodic/EnumerationTenFixed.golden_fixed_point_block_counts_ten`
- Truth anchor: `D5/S0/Tower/GoldenPeriodic/EnumerationTenFixed.golden_fixed_point_codes_ten_decompose`
- Dependency: [D5/S0/Tower/GoldenPeriodic/EnumerationTenData](EnumerationTenData.md)
