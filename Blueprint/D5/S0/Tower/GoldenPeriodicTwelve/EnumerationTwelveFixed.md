# Period-Twelve Fixed-Point Decomposition

## Abstract

The 322 period-twelve fixed equations decompose into 21 prefix blocks.

Every block contains only eight, thirteen, or twenty-one exact affine fixed equations.

**Theorem 1.1 (There are exactly 322 period-twelve fixed codes).**

$$\operatorname{length}\left(\operatorname{goldenFixedPointCodes}\left(12\right)\right) = 322$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/GoldenPeriodicTwelve/EnumerationTwelveFixed.golden_fixed_point_code_count_exactly_twelve` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The twenty-one prefix-block counts sum exactly to 322.

**Theorem 1.2 (Every period-twelve fixed point is an enumerated phase).**

$$\operatorname{toFinset}\left(\operatorname{goldenFixedPointCodes}\left(12\right)\right) = \mathit{goldenExpectedPointCodesTwelve}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/GoldenPeriodicTwelve/EnumerationTwelveFixed.golden_fixed_point_codes_twelve_decompose` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact fixed-point codes equal all inherited phases and all 300 phases on the primitive twelve-cycles.

## References

- Truth anchor: `D5/S0/Tower/GoldenPeriodicTwelve/EnumerationTwelveFixed.golden_fixed_point_code_count_exactly_twelve`
- Truth anchor: `D5/S0/Tower/GoldenPeriodicTwelve/EnumerationTwelveFixed.golden_fixed_point_codes_twelve_decompose`
- Dependency: [D5/S0/Tower/GoldenPeriodicTwelve/EnumerationTwelveSeparation](EnumerationTwelveSeparation.md)
