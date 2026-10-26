# Profile rigidity in geometric equality

## Abstract

A unique profile peak forces troughs onto physical endpoints.

**Definition 1.1 (The original row profile).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraEqualityProfile.profile`

*Formalization.* `D5/S3/Combinatorics/Geometry/MiuraEqualityProfile.profile` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The one-row array retains the values of a specified actual row and every existing horizontal neighbour. Its endpoints count as possible local extrema.

**Theorem 1.2 (One peak excludes internal troughs).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraEqualityProfile.unique_profile_peak_minima_on_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraEqualityProfile.unique_profile_peak_minima_on_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every integer unit-edge array with a specified actual row, if its row profile has exactly one local maximum including endpoints, every local minimum of that profile lies at the first or last physical column. The attained finite maximum envelope makes the entire profile a tent with its peak at that unique maximum. An internal vertex of such a tent cannot have both adjacent vertices higher.

**Theorem 1.3 (A first reversal produces a physical-side minimum).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraEqualityProfile.reversal_after_unique_peak_on_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraEqualityProfile.reversal_after_unique_peak_on_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At an internal row of an actual unit-edge array, suppose the preceding full cut descends, at least one next edge ascends, and the current row profile has exactly one local maximum including endpoints. Then an actual ambient minimum lies on the first or last physical column of this row. The negated first-reversal theorem gives an ambient minimum; its horizontal minimum property and the unique-peak result put it at an endpoint.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraEqualityProfile.profile`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraEqualityProfile.reversal_after_unique_peak_on_boundary`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraEqualityProfile.unique_profile_peak_minima_on_boundary`
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraStripRigidity](MiuraStripRigidity.md)
