# The geometric frozen-run bound

## Abstract

The sum of actual frozen run counts is bounded by the number of individual extrema.

**Theorem 1.1 (The actual slab count).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraSlabRunBound.actual_slab_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraSlabRunBound.actual_slab_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every integer unit-edge array with at least two rows and two columns, if both axes have an unoccupied row in their respective orientation, the sum of the actual row and column occupied slab counts is at most its number of individual extrema plus two. The proof combines the exhaustive actual slab partition, existence of both nonneutral types, and the individual-extremum charging theorem.

**Definition 1.2 (Actual frozen run starts).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraSlabRunBound.FrozenRowRunStart`

*Formalization.* `D5/S3/Combinatorics/Geometry/MiuraSlabRunBound.FrozenRowRunStart` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An actual frozen run starts at an unoccupied row that is either the physical first row or immediately follows an occupied row. Thus each maximal consecutive unoccupied interval has one start.

**Theorem 1.3 (Exact slab and run count relation).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraSlabRunBound.slab_card_eq_frozen_runs_add_one`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraSlabRunBound.slab_card_eq_frozen_runs_add_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every unit-edge array with at least two rows and one column, the number of actual occupied row slabs is exactly one more than the number of frozen row runs. Each nonterminal occupied slab is paired bijectively with the immediately following frozen run start; physical boundary occupancy supplies the unique terminal slab.

**Theorem 1.4 (The incidence consequences of run equality).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraSlabRunBound.frozen_run_equality_incidence`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraSlabRunBound.frozen_run_equality_incidence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When an actual array has as many individual extrema as frozen runs on both axes together, the neutral row and column extremum supports coincide and their slab counts agree. The product of the minimum row slab count minus one with the minimum column slab count minus one vanishes, as does the corresponding maximum product. These consequences use saturation of the full individual-extremum charge; the common-side or four-extremum classification remains a further geometric statement.

**Theorem 1.5 (The uniform geometric run bound).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraSlabRunBound.frozen_runs_le_extrema`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraSlabRunBound.frozen_runs_le_extrema` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every actual integer unit-edge array with at least two rows and two columns and with a frozen row and a frozen column, the sum of its frozen row run count and frozen column run count is at most the number of its individual ambient extrema. Normalization and any comparison between its minimum and maximum counts are unnecessary. This bound does not classify its equality cases.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraSlabRunBound.FrozenRowRunStart`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraSlabRunBound.actual_slab_bound`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraSlabRunBound.frozen_run_equality_incidence`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraSlabRunBound.frozen_runs_le_extrema`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraSlabRunBound.slab_card_eq_frozen_runs_add_one`
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraSlabBudget](MiuraSlabBudget.md)
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraSlabCover](MiuraSlabCover.md)
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraSlabSigns](MiuraSlabSigns.md)
