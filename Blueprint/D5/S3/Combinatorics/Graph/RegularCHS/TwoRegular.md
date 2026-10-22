# Cycle partitions

## Abstract

Complete homogeneous coefficient domination for two-regular graphs.

**Definition 1.1 (The squared geometric cycle factor).**

Lean statement: `D5/S3/Combinatorics/Graph/RegularCHS/TwoRegular.cycleKernel`

*Formalization.* `D5/S3/Combinatorics/Graph/RegularCHS/TwoRegular.cycleKernel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ángel Chávez, Sarah Fullerton, Matilda LaFortune, Keyron Linarez, Nethmin Liyanage, Justin Son and Tyler Ting (2023). *Extremal polynomial norms of graphs*. DOI: [10.48550/arXiv.2311.04689](https://doi.org/10.48550/arXiv.2311.04689). URL: <https://arxiv.org/abs/2311.04689v3>.

*Commentary.*

The series cycleKernel l is obtained from the series with coefficient k plus one by substituting X to the power l. For positive l its coefficient in degree k equals k divided by l plus one when l divides k, and zero otherwise; the division is natural-number division.

**Theorem 1.2 (Partitioning a cycle length increases denominator coefficients).**

Lean statement: `D5/S3/Combinatorics/Graph/RegularCHS/TwoRegular.cycleKernel_sum_le_prod`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/RegularCHS/TwoRegular.cycleKernel_sum_le_prod` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ángel Chávez, Sarah Fullerton, Matilda LaFortune, Keyron Linarez, Nethmin Liyanage, Justin Son and Tyler Ting (2023). *Extremal polynomial norms of graphs*. DOI: [10.48550/arXiv.2311.04689](https://doi.org/10.48550/arXiv.2311.04689). URL: <https://arxiv.org/abs/2311.04689v3>.

*Commentary.*

For any nonempty finite list of positive lengths, every coefficient of the cycle factor at their sum is at most the corresponding coefficient of the product of their cycle factors. To merge two lengths a and b, a nonzero coefficient on the left has degree (a+b)j and value j+1. The convolution on the right contains the term with degrees aj and bj, whose value is (j+1) squared. All other terms are nonnegative. Induction merges any finite partition.

The comparison is preserved by substitution of the odd Catalan series and multiplication by the common nonnegative numerator. These operations connect the factors to the complete homogeneous coefficients of cycle components.

**Theorem 1.3 (Cycle domination for two-regular graphs).**

Lean statement: `D5/S3/Combinatorics/Graph/RegularCHS/TwoRegular.chs_cycle_le_twoRegular`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/RegularCHS/TwoRegular.chs_cycle_le_twoRegular` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ángel Chávez, Sarah Fullerton, Matilda LaFortune, Keyron Linarez, Nethmin Liyanage, Justin Son and Tyler Ting (2023). *Extremal polynomial norms of graphs*. DOI: [10.48550/arXiv.2311.04689](https://doi.org/10.48550/arXiv.2311.04689). URL: <https://arxiv.org/abs/2311.04689v3>.

*Commentary.*

For every two-regular simple graph on n vertices, with n at least three, every adjacency complete homogeneous coefficient is at least the corresponding coefficient of the cycle on n vertices. The graph may be disconnected and the degree of the coefficient may be odd or zero.

Degree two passes to each connected component through an explicit equivalence of neighbor sets. Each component contains a cycle, and the connected degree-two cycle-isomorphism theorem in the Brooks module identifies that component with a cycle of length at least three. The component lengths sum to n, and the adjacency pencil determinant factors over the components.

Let q be the odd Catalan series, which satisfies q = t times (1 plus q squared). The cleared adjacency pencil of a cycle of length l has determinant (1 minus q to the power l) squared. The Hermitian determinant formula and the complete homogeneous series product identify the graph series with (1 plus q squared) to the power n times the product of the substituted cycle factors. The single cycle has the same numerator and the factor at the sum of the component lengths. The coefficient partition theorem, nonnegative substitution, and multiplication by the common numerator prove the comparison.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/RegularCHS/TwoRegular.chs_cycle_le_twoRegular`
- Truth anchor: `D5/S3/Combinatorics/Graph/RegularCHS/TwoRegular.cycleKernel`
- Truth anchor: `D5/S3/Combinatorics/Graph/RegularCHS/TwoRegular.cycleKernel_sum_le_prod`
- Dependency: [D5/S0/Observation/MatrixTracePowerSum](../../../../S0/Observation/MatrixTracePowerSum.md)
- Dependency: [D5/S3/Combinatorics/Graph/Brooks/General](../Brooks/General.md)
- Dependency: [D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormClosedForm](../PathCHS/PathCHSNormClosedForm.md)
- Dependency: [D5/S3/Combinatorics/Graph/RegularCHS/Defs](Defs.md)
- Dependency: [D5/S3/Combinatorics/SpectralGraph/CyclicTridiagonalTransferTrace](../../SpectralGraph/CyclicTridiagonalTransferTrace.md)
- Dependency: [D5/S3/Quantum/FockSpace/ForbiddenNeighbourDeterminant](../../../Quantum/FockSpace/ForbiddenNeighbourDeterminant.md)
