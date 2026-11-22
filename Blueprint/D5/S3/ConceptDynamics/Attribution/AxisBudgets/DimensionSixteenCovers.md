# Rank bounds for a sixteen-coordinate fixed-seed budget

## Abstract

Bound the fixed-seed costs of full inclusion and inclusion covers in dimension sixteen.

**Definition 1.1 (A feasible factor supported on diagonals and inclusion covers).**

$$\forall b \in \mathrm{Nat},\; \operatorname{CoverWithin}\left(b\right) \Leftrightarrow \left(\exists f \in \operatorname{BinaryEdgeTables}\left(15\right),\; \exists s \in \mathrm{Bool},\; \operatorname{CoverSupport}\left(f\right) \land \left(\operatorname{CoverDegrees}\left(f, s\right) \land \operatorname{AxisCost}\left(f\right) \le b\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Attribution/AxisBudgets/DimensionSixteenCovers.coverWithin` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fix coordinate zero in dimension sixteen and multiplier three. BinaryEdgeTables(15) is the set of Boolean edge tables on two copies of the subsets of the other fifteen coordinates. CoverSupport(f) excludes the edge from the full set to itself. Any positive entry outside the full-set row must be diagonal or add exactly one element. CoverDegrees(f,s) requires each ordinary row and column to have odd degree at most three. Both full-set vertices have even degree at most two if s is true, and odd degree at most one if s is false. AxisCost(f) is four times the sum of one and the number of selected edges from ordinary odd-rank rows to odd-rank columns.

**Theorem 1.2 (Every factor on diagonals and inclusion covers requires at least 2044).**

$$\forall b \in \mathrm{Nat},\; \operatorname{CoverWithin}\left(b\right) \Rightarrow 2044 \le b$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/AxisBudgets/DimensionSixteenCovers.cover_budget_ge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If at most one exceptional edge enters the first four layers, the first and third ranks each pay an additional diagonal unit. If two enter, the odd cardinalities and the rank-cut parity at ranks five, seven and nine force three additional diagonal units. Thus at least 510 ordinary edges are charged. The marked column contributes one unit.

**Theorem 1.3 (Full inclusion requires at least 2036 fixed seeds).**

$$\forall b \in \mathrm{Nat},\; \operatorname{AxisFactorWithin}\left(3, 0, b\right) \Rightarrow 2036 \le b$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/AxisBudgets/DimensionSixteenCovers.full_budget_ge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The low-side deficits at ranks one and three and the high-side deficits at ranks eleven and thirteen force 508 charged ordinary edges. The marked edge accounts for one more unit and a unit is four fixed seeds.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/AxisBudgets/DimensionSixteenCovers.coverWithin`
- Truth anchor: `D5/S3/ConceptDynamics/Attribution/AxisBudgets/DimensionSixteenCovers.cover_budget_ge`
- Truth anchor: `D5/S3/ConceptDynamics/Attribution/AxisBudgets/DimensionSixteenCovers.full_budget_ge`
- Dependency: [D5/S3/Combinatorics/Graph/RankCuts/RankedBipartiteCapacity](../../../Combinatorics/Graph/RankCuts/RankedBipartiteCapacity.md)
- Dependency: [D5/S3/Combinatorics/Graph/RankCuts/RankedBipartiteDiagonalParity](../../../Combinatorics/Graph/RankCuts/RankedBipartiteDiagonalParity.md)
- Dependency: [D5/S3/ConceptDynamics/Attribution/ParitySeedAxisFactor](../ParitySeedAxisFactor.md)
