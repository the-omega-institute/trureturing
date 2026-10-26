# Charging actual slab types to individual extremum cells

## Abstract

Charging actual slab types to individual extremum cells

**Definition 1.1 (Extrema with a neutral endpoint).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraSlabBudget.neutralSupport`

*Formalization.* `D5/S3/Combinatorics/Geometry/MiuraSlabBudget.neutralSupport` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the union of the individual extremum cells in neutral row slabs and those in neutral column slabs. A cell in both sets remains one cell.

**Theorem 1.2 (Neutral vertex budget).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraSlabBudget.neutral_slab_budget`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraSlabBudget.neutral_slab_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every actual integer unit-edge array with at least two rows, the sum of the neutral row and column slab counts is at most the number of extrema with at least one neutral endpoint. Each neutral slab has two distinct incidences and each actual extremum has at most two neutral endpoints.

**Theorem 1.3 (Equality keeps both endpoints neutral).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraSlabBudget.neutral_budget_equality`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraSlabBudget.neutral_budget_equality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the neutral support cardinality equals the total neutral row and column slab count, the row and column neutral supports coincide, and the two neutral slab counts are equal. Thus every extremum with one neutral endpoint has a neutral endpoint on the other axis too.

**Theorem 1.4 (Matching nonneutral rectangles).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraSlabBudget.matching_slab_budget`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraSlabBudget.matching_slab_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every actual unit-edge array with at least two rows and one column, the product of minimum row and column slab counts plus the analogous maximum product is at most the number of individual extrema outside the neutral support. Each rectangle supplies a minimum or maximum, distinct rectangles give distinct cells by actual slab uniqueness, and minimum and maximum witnesses cannot coincide.

**Theorem 1.5 (Equality excludes a single neutral endpoint).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraSlabBudget.slab_budget_equality`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraSlabBudget.slab_budget_equality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the total individual extremum count equals the sum of the two neutral slab counts and the two matching-type products, every extremum incident with a neutral row slab is incident with a neutral column slab and conversely. The two neutral slab counts are equal. This is a consequence of saturation of the actual charge; it does not by itself classify geometric equality.

**Theorem 1.6 (Full actual slab charge).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraSlabBudget.slab_extremum_budget`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraSlabBudget.slab_extremum_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every actual unit-edge array with at least two rows and one column, its total individual extremum count is at least the sum of its two neutral slab counts, the product of its minimum row and column slab counts, and the product of its maximum row and column slab counts. These are canonical interval families of the same array, with no independent incidence graph supplied.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraSlabBudget.matching_slab_budget`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraSlabBudget.neutralSupport`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraSlabBudget.neutral_budget_equality`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraSlabBudget.neutral_slab_budget`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraSlabBudget.slab_budget_equality`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraSlabBudget.slab_extremum_budget`
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraSlabIncidence](MiuraSlabIncidence.md)
