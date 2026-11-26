# Extract a coloured table from an even-dimensional seed action

## Abstract

Extract coloured parity multiplicities and coordinate bounds from one seed action.

**Theorem 1.1 (Coloured multiplicities under coordinate fixed-count bounds).**

$$\operatorname{EvenDimensionalSeedCounts}\left(d, k, z\right) \Rightarrow \operatorname{BoundedColouredTable}\left(d, k, z\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/ParityColouredTableExtraction.extract_coloured_subsets` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let d be even and at least two, let k be a natural number, and suppose a common equivariant action on k times 2 raised to the power (d + 1) seeds realizes the coordinate fixed-count vector z with uniform coloured marginals. There is a table of nonnegative integer multiplicities for an even subset, an odd subset, and a left colour.

Each even subset and left colour has marginal k. Each odd subset has marginal 2k after summing over even subsets and both left colours. The two left-colour entries coincide away from the full even subset. At every coordinate i, twice the sum of the entries modulo two over pairs of subsets both containing i and both left colours is at most z(i).

Right colours lie in the same output orbit for any fixed left colour. An ordinary even subset lets the action change the left colour independently. These orbit identities give the marginal equations for the table of fibre sizes. On a fixed output point, the coordinate-fixed seed count has the same parity as the fibre size. Summing the least compatible counts gives the bound.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/ParityColouredTableExtraction.extract_coloured_subsets`
- Dependency: [D5/S3/ConceptDynamics/Attribution/CoordinateColourOrbit](CoordinateColourOrbit.md)
- Dependency: [D5/S3/ConceptDynamics/Attribution/CoordinateFibreCounts](CoordinateFibreCounts.md)
- Dependency: [D5/S3/ConceptDynamics/Attribution/ParityOddRankBounds](ParityOddRankBounds.md)
- Dependency: [D5/S3/ConceptDynamics/Attribution/ParitySeedOptimization](ParitySeedOptimization.md)
- Dependency: [D5/S3/ConceptDynamics/Attribution/ParityThreeOrbitTable](ParityThreeOrbitTable.md)
