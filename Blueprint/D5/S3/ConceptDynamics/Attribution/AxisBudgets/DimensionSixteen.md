# A sixteen-coordinate budget that requires an edge skipping ranks

## Abstract

Compare full inclusion and inclusion covers in the one-coordinate Boolean lattice.

**Definition 1.1 (A feasible factor supported on diagonals and inclusion covers).**

$$\forall b \in \mathrm{Nat},\; \operatorname{CoverWithin}\left(b\right) \Leftrightarrow \left(\exists f \in \operatorname{BinaryEdgeTables}\left(15\right),\; \exists s \in \mathrm{Bool},\; \operatorname{CoverSupport}\left(f\right) \land \left(\operatorname{CoverDegrees}\left(f, s\right) \land \operatorname{AxisCost}\left(f\right) \le b\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Attribution/AxisBudgets/DimensionSixteen.coverWithin` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fix coordinate zero in dimension sixteen and multiplier three. BinaryEdgeTables(15) is the set of Boolean edge tables on two copies of the subsets of the other fifteen coordinates. CoverSupport(f) excludes the edge from the full set to itself. Any positive entry outside the full-set row must be diagonal or add exactly one element. CoverDegrees(f,s) requires each ordinary row and column to have odd degree at most three. Both full-set vertices have even degree at most two if s is true, and odd degree at most one if s is false. AxisCost(f) is four times the sum of one and the number of selected edges from ordinary odd-rank rows to odd-rank columns.

**Theorem 1.2 (The full inclusion graph has minimum budget 2036).**

$$\forall b \in \mathrm{Nat},\; \operatorname{AxisFactorWithin}\left(3, 0, b\right) \Leftrightarrow 2036 \le b$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/AxisBudgets/DimensionSixteen.full_budget_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The rank-capacity inequality charges at least 11, 211, 213 and 73 ordinary edges at ranks one, three, eleven and thirteen. The marked contribution raises the normalized cost from 508 to 509. A checked binary factor attains this bound. Its only ordinary edge spanning multiple ranks goes from the first four available coordinates to the first ten.

**Theorem 1.3 (Every factor on diagonals and inclusion covers requires at least 2044).**

$$\forall b \in \mathrm{Nat},\; \operatorname{CoverWithin}\left(b\right) \Rightarrow 2044 \le b$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/AxisBudgets/DimensionSixteen.cover_budget_ge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If at most one exceptional edge enters the first four layers, the first and third ranks each pay an additional diagonal unit. If two enter, the odd cardinalities and the rank-cut parity at ranks five, seven and nine force three additional diagonal units. Thus at least 510 ordinary edges are charged. The marked column contributes one unit.

**Definition 1.4 (The adjacent-rank assertion at budget 2036).**

$$\operatorname{AxisFactorWithin}\left(3, 0, 2036\right) \Rightarrow \operatorname{CoverWithin}\left(2036\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Attribution/AxisBudgets/DimensionSixteen.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The assertion says that feasibility at budget 2036 in the full inclusion graph entails feasibility on diagonals and inclusion covers.

**Theorem 1.5 (The adjacent-rank assertion is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/AxisBudgets/DimensionSixteen.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The full graph has a feasible factor at budget 2036. A cover factor with this budget would give the incompatible inequalities 2044 at most the budget and the budget at most 2036.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/AxisBudgets/DimensionSixteen.claim`
- Truth anchor: `D5/S3/ConceptDynamics/Attribution/AxisBudgets/DimensionSixteen.coverWithin`
- Truth anchor: `D5/S3/ConceptDynamics/Attribution/AxisBudgets/DimensionSixteen.cover_budget_ge`
- Truth anchor: `D5/S3/ConceptDynamics/Attribution/AxisBudgets/DimensionSixteen.full_budget_iff`
- Truth anchor: `D5/S3/ConceptDynamics/Attribution/AxisBudgets/DimensionSixteen.result`
- Dependency: [D5/S3/Combinatorics/ErdosUlam/SublatticeDefs](../../../Combinatorics/ErdosUlam/SublatticeDefs.md)
- Dependency: [D5/S3/Combinatorics/Graph/RankCuts/RankedBipartiteCapacity](../../../Combinatorics/Graph/RankCuts/RankedBipartiteCapacity.md)
- Dependency: [D5/S3/Combinatorics/Graph/RankCuts/RankedBipartiteDiagonalParity](../../../Combinatorics/Graph/RankCuts/RankedBipartiteDiagonalParity.md)
- Dependency: [D5/S3/ConceptDynamics/Attribution/ParitySeedAxisFactor](../ParitySeedAxisFactor.md)
