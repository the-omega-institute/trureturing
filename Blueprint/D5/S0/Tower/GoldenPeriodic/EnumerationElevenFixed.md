# Period-Eleven Fixed-Point Decomposition

## Abstract

The 199 period-eleven fixed equations decompose into eight prefix blocks.

The three 34-equation blocks are each refined into fourth-step subblocks of size twenty-one and thirteen before exact comparison.

**Theorem 1.1 (The eight fixed-point blocks have exact sizes).**

$$\operatorname{periodElevenFixedBlockLengths}\left(\right) = \operatorname{list}\left(34, 21, 34, 34, 21, 21, 13, 21\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/GoldenPeriodic/EnumerationElevenFixed.golden_fixed_point_block_counts_eleven` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The block sizes are 34, 21, 34, 34, 21, 21, 13, and 21.

**Theorem 1.2 (Every period-eleven fixed point is an enumerated phase).**

$$\operatorname{toFinset}\left(\operatorname{goldenFixedPointCodes}\left(11\right)\right) = \mathit{goldenExpectedPointCodesEleven}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/GoldenPeriodic/EnumerationElevenFixed.golden_fixed_point_codes_eleven_decompose` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact fixed-point codes equal the inherited fixed phase and all 198 phases on the primitive eleven-cycles.

## References

- Truth anchor: `D5/S0/Tower/GoldenPeriodic/EnumerationElevenFixed.golden_fixed_point_block_counts_eleven`
- Truth anchor: `D5/S0/Tower/GoldenPeriodic/EnumerationElevenFixed.golden_fixed_point_codes_eleven_decompose`
- Dependency: [D5/S0/Tower/GoldenPeriodic/EnumerationElevenSeparation](EnumerationElevenSeparation.md)
