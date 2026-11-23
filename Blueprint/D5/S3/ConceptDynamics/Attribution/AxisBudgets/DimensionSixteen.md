# A sixteen-coordinate budget that requires an edge skipping ranks

## Abstract

Compare full inclusion and inclusion covers in the one-coordinate Boolean lattice.

**Theorem 1.1 (The full inclusion graph has minimum budget 2036).**

$$\forall b \in \mathrm{Nat},\; \operatorname{AxisFactorWithin}\left(3, 0, b\right) \Leftrightarrow 2036 \le b$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/AxisBudgets/DimensionSixteen.full_budget_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The rank-capacity inequality charges at least 11, 211, 213 and 73 ordinary edges at ranks one, three, eleven and thirteen. The marked contribution raises the normalized cost from 508 to 509. A checked binary factor attains this bound. Its only ordinary edge spanning multiple ranks goes from the first four available coordinates to the first ten.

**Definition 1.2 (The adjacent-rank assertion at budget 2036).**

$$\operatorname{AxisFactorWithin}\left(3, 0, 2036\right) \Rightarrow \operatorname{CoverWithin}\left(2036\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Attribution/AxisBudgets/DimensionSixteen.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The assertion says that feasibility at budget 2036 in the full inclusion graph entails feasibility on diagonals and inclusion covers.

**Theorem 1.3 (The adjacent-rank assertion is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/AxisBudgets/DimensionSixteen.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The full graph has a feasible factor at budget 2036. A cover factor with this budget would give the incompatible inequalities 2044 at most the budget and the budget at most 2036.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/AxisBudgets/DimensionSixteen.claim`
- Truth anchor: `D5/S3/ConceptDynamics/Attribution/AxisBudgets/DimensionSixteen.full_budget_iff`
- Truth anchor: `D5/S3/ConceptDynamics/Attribution/AxisBudgets/DimensionSixteen.result`
- Dependency: [D5/S3/Combinatorics/ErdosUlam/SublatticeDefs](../../../Combinatorics/ErdosUlam/SublatticeDefs.md)
- Dependency: [D5/S3/ConceptDynamics/Attribution/AxisBudgets/AxisListCertificate](AxisListCertificate.md)
- Dependency: [D5/S3/ConceptDynamics/Attribution/AxisBudgets/DimensionSixteenCovers](DimensionSixteenCovers.md)
- Dependency: [D5/S3/ConceptDynamics/Attribution/ParitySeedAxisFactor](../ParitySeedAxisFactor.md)
