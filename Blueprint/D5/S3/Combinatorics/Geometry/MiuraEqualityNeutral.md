# MiuraEqualityNeutral

## Abstract

Actual-array geometric equality for the original Miura residual class.

**Theorem 1.1 (equality neutral extremum interior).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraEqualityNeutral.equality_neutral_extremum_interior`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraEqualityNeutral.equality_neutral_extremum_interior` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every actual integer unit-edge height array on an m by n grid with both dimensions at least two, suppose that each axis has a genuinely unoccupied row and that the individual-extremum count equals the sum of the actual frozen row-run count and the actual frozen column-run count. Every individual extremum belonging to the actual neutral-row support is strictly internal on both physical axes: its row index is positive and its successor is less than m, and its column index is positive and its successor is less than n.

**Theorem 1.2 (equality first minimum in minimum slab).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraEqualityNeutral.equality_first_minimum_in_minimum_slab`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraEqualityNeutral.equality_first_minimum_in_minimum_slab` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every actual integer unit-edge height array on an m by n grid with both dimensions at least two, suppose that each axis has a genuinely unoccupied row and that the individual-extremum count equals the sum of the actual frozen row-run count and the actual frozen column-run count. If the physical top-row profile has exactly one one-dimensional local maximum, including endpoints, then any specified ambient minimum whose row precedes no other ambient minimum belongs to a minimum-type row slab. A minimum-free prefix is a descending extrusion of the same top profile; the profile minimum is therefore at a physical column endpoint, where equality forbids neutral incidence.

**Theorem 1.3 (equality no neutral of boundary peaks).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraEqualityNeutral.equality_no_neutral_of_boundary_peaks`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraEqualityNeutral.equality_no_neutral_of_boundary_peaks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every actual integer unit-edge height array on an m by n grid with both dimensions at least two, suppose that each axis has a genuinely unoccupied row and that the individual-extremum count equals the sum of the actual frozen row-run count and the actual frozen column-run count. If there is exactly one minimum row slab and the actual physical top and bottom profiles each have exactly one one-dimensional local maximum, then both the neutral row-slab family and the neutral column-slab family are empty. The earliest and latest ambient minima belong to the same minimum slab and bound all actual minima. Every hypothetical neutral slab supplies an actual minimum, contradicting disjointness of the canonical slabs.

**Theorem 1.4 (equality boundary maximum profiles).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraEqualityNeutral.equality_boundary_maximum_profiles`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraEqualityNeutral.equality_boundary_maximum_profiles` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every actual integer unit-edge height array on an m by n grid with both dimensions at least two, suppose that each axis has a genuinely unoccupied row and that the individual-extremum count equals the sum of the actual frozen row-run count and the actual frozen column-run count. If there is exactly one maximum column slab and specified maximum row slabs contain the physical first and last rows, respectively, then the physical top and bottom profiles each have exactly one local maximum including endpoints. Saturation supplies unique actual maxima; boundary strip rigidity lifts every profile maximum to an ambient maximum in its specified slab.

**Theorem 1.5 (equality crossed no neutral).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraEqualityNeutral.equality_crossed_no_neutral`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraEqualityNeutral.equality_crossed_no_neutral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every actual integer unit-edge height array on an m by n grid with both dimensions at least two, suppose that each axis has a genuinely unoccupied row and that the individual-extremum count equals the sum of the actual frozen row-run count and the actual frozen column-run count. If there is exactly one minimum row slab and exactly one maximum column slab, and specified maximum row slabs contain the physical first and last rows, respectively, then both actual neutral slab families are empty. The required profile uniqueness is derived from these actual boundary slabs.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraEqualityNeutral.equality_boundary_maximum_profiles`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraEqualityNeutral.equality_crossed_no_neutral`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraEqualityNeutral.equality_first_minimum_in_minimum_slab`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraEqualityNeutral.equality_neutral_extremum_interior`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraEqualityNeutral.equality_no_neutral_of_boundary_peaks`
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraEqualityProfile](MiuraEqualityProfile.md)
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraEqualitySaturation](MiuraEqualitySaturation.md)
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraSlabRunBound](MiuraSlabRunBound.md)
