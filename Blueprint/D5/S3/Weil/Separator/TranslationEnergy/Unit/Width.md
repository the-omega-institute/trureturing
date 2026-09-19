# Width of the rounded unit aggregate

## Abstract

Width of the rounded unit aggregate.

**Theorem 1.1 (The integrand width).**

Lean statement: `D5/S3/Weil/Separator/TranslationEnergy/Unit/Width.unit_cell_width`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Separator/TranslationEnergy/Unit/Width.unit_cell_width` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive natural R and every ordered rational cell of length ell, the actual rounded unit payload at precision m and Taylor depth 4m+4 has norm-square interval width at most 72 ell/R+16*2^-m+16*2^-32. The cutoff intervals stay in [0,1] after outward rounding, so each signed difference lies in [-1,1].

**Theorem 1.2 (The full aggregate width).**

Lean statement: `D5/S3/Weil/Separator/TranslationEnergy/Unit/Width.unit_aggregate_width`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Separator/TranslationEnergy/Unit/Width.unit_aggregate_width` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every rational shift and mesh depth d, let L be the actual support hull length. Summing the cell bounds gives aggregate width at most (72/R)(L/2^d)L+(16*2^-m+16*2^-32)L. This uses the actual mapped payload list, total length and squared-length bound.

## References

- Truth anchor: `D5/S3/Weil/Separator/TranslationEnergy/Unit/Width.unit_aggregate_width`
- Truth anchor: `D5/S3/Weil/Separator/TranslationEnergy/Unit/Width.unit_cell_width`
- Dependency: [D5/S3/Weil/Separator/TranslationEnergy/CutoffIntervals](../CutoffIntervals.md)
- Dependency: [D5/S3/Weil/Separator/TranslationEnergy/SignedSquares](../SignedSquares.md)
- Dependency: [D5/S3/Weil/Separator/TranslationEnergy/UnitAcceptance](../UnitAcceptance.md)
