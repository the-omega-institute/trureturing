# Two-sided finite pencil reduction

## Abstract

Finite extraction of right and left singular pencil summands

A finite pencil is a pair of linear maps between finite-dimensional vector spaces over a field. Repeatedly split off a shortest polynomial right-kernel chain. Each step supplies actual commuting projections and lowers the remaining source dimension. Apply the same construction to the dual of the right-reduced remainder to extract left singular blocks. The final pair has no polynomial kernel chain on either side and has equal source and target dimensions.

The reduction constructs the singular direct summands internally. It does not assume a Kronecker canonical form or the existence of an invertible linear combination for the final square pair. Polynomial regularity of that square pair is a separate statement. The degree zero blocks remain present as common zero rows or columns.

**Definition 1.1 (A finite-dimensional two-arrow pencil).**

Lean statement: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.Pencil`

*Formalization.* `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.Pencil` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* N. Wang; L. Chen (2025). *Equality condition for a matrix inequality by partial transpose*. DOI: [10.1142/S1230161226500071](https://doi.org/10.1142/S1230161226500071). URL: <https://arxiv.org/abs/2508.18644v1>.

*Commentary.*

The data consists of finite-dimensional source and target vector spaces over the field and two linear arrows between them. The source and target may both have dimension zero.

**Definition 1.2 (Duality reverses both arrows).**

Lean statement: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.dual`

*Formalization.* `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.dual` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* N. Wang; L. Chen (2025). *Equality condition for a matrix inequality by partial transpose*. DOI: [10.1142/S1230161226500071](https://doi.org/10.1142/S1230161226500071). URL: <https://arxiv.org/abs/2508.18644v1>.

*Commentary.*

Replace the source by the dual of the target, the target by the dual of the source, and each arrow by its linear dual. No complex conjugation is involved.

**Definition 1.3 (Absence of polynomial right-kernel chains).**

Lean statement: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.RightReduced`

*Formalization.* `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.RightReduced` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* N. Wang; L. Chen (2025). *Equality condition for a matrix inequality by partial transpose*. DOI: [10.1142/S1230161226500071](https://doi.org/10.1142/S1230161226500071). URL: <https://arxiv.org/abs/2508.18644v1>.

*Commentary.*

Every finite coefficient chain satisfying all pencil boundary equations has zero final coefficient. Repeated removal of trailing zeros makes this equivalent to the absence of any nonzero polynomial right-kernel vector.

**Definition 1.4 (An actual shortest-chain summand).**

Lean statement: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.SplitData`

*Formalization.* `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.SplitData` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* N. Wang; L. Chen (2025). *Equality condition for a matrix inequality by partial transpose*. DOI: [10.1142/S1230161226500071](https://doi.org/10.1142/S1230161226500071). URL: <https://arxiv.org/abs/2508.18644v1>.

*Commentary.*

A chain of index r is accompanied by its nonzero endpoint, boundary equations, independent source and image chains, and projections onto their spans. Both arrows intertwine the two projections.

**Definition 1.5 (The simultaneous complementary pencil).**

Lean statement: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.remainder`

*Formalization.* `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.remainder` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* N. Wang; L. Chen (2025). *Equality condition for a matrix inequality by partial transpose*. DOI: [10.1142/S1230161226500071](https://doi.org/10.1142/S1230161226500071). URL: <https://arxiv.org/abs/2508.18644v1>.

*Commentary.*

Restrict the arrows to the kernels of the source and target chain projections. Their commuting identities ensure both restrictions map into the target kernel.

**Definition 1.6 (A finite right singular reduction tree).**

Lean statement: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.RightReduction`

*Formalization.* `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.RightReduction` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* N. Wang; L. Chen (2025). *Equality condition for a matrix inequality by partial transpose*. DOI: [10.1142/S1230161226500071](https://doi.org/10.1142/S1230161226500071). URL: <https://arxiv.org/abs/2508.18644v1>.

*Commentary.*

A leaf is right-reduced. An internal node consists of an actual right-chain split and a reduction of its simultaneous complement.

**Definition 1.7 (Left extraction after right reduction).**

Lean statement: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.LeftReduction`

*Formalization.* `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.LeftReduction` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* N. Wang; L. Chen (2025). *Equality condition for a matrix inequality by partial transpose*. DOI: [10.1142/S1230161226500071](https://doi.org/10.1142/S1230161226500071). URL: <https://arxiv.org/abs/2508.18644v1>.

*Commentary.*

Each stage remains right-reduced. A leaf is right-reduced on both sides and square. An internal node extracts a right chain from the dual, corresponding to a left singular block in the original pencil.

**Definition 1.8 (A finite two-sided singular reduction tree).**

Lean statement: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.TwoSidedReduction`

*Formalization.* `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.TwoSidedReduction` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* N. Wang; L. Chen (2025). *Equality condition for a matrix inequality by partial transpose*. DOI: [10.1142/S1230161226500071](https://doi.org/10.1142/S1230161226500071). URL: <https://arxiv.org/abs/2508.18644v1>.

*Commentary.*

Right singular splits precede a finite left reduction. Every split uses actual complementary maps, and each final pair is square with no polynomial kernel chain on either side.

**Theorem 1.9 (Every finite pencil admits two-sided extraction).**

Lean statement: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.two_sided_reduction`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.two_sided_reduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* N. Wang; L. Chen (2025). *Equality condition for a matrix inequality by partial transpose*. DOI: [10.1142/S1230161226500071](https://doi.org/10.1142/S1230161226500071). URL: <https://arxiv.org/abs/2508.18644v1>.

*Commentary.*

First obtain the finite right reduction. At each right-reduced leaf apply the finite left reduction. The resulting tree decomposes the pair into right and left singular chain summands and square two-sided reduced remainders.

**Definition 1.10 (Rank of the two-term tensor map).**

Lean statement: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.tensorRank`

*Formalization.* `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.tensorRank` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* N. Wang; L. Chen (2025). *Equality condition for a matrix inequality by partial transpose*. DOI: [10.1142/S1230161226500071](https://doi.org/10.1142/S1230161226500071). URL: <https://arxiv.org/abs/2508.18644v1>.

*Commentary.*

For two finite complex pencils p and q, take the image dimension of p.first tensor q.first plus p.second tensor q.second. The tensor factor order is fixed throughout.

**Definition 1.11 (Rank of the horizontal pair map).**

Lean statement: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.horizontalRank`

*Formalization.* `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.horizontalRank` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* N. Wang; L. Chen (2025). *Equality condition for a matrix inequality by partial transpose*. DOI: [10.1142/S1230161226500071](https://doi.org/10.1142/S1230161226500071). URL: <https://arxiv.org/abs/2508.18644v1>.

*Commentary.*

The image dimension of the linear map from two copies of the source that sends (x,y) to first(x)+second(y).

**Definition 1.12 (Rank of the joint output map).**

Lean statement: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.verticalRank`

*Formalization.* `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.verticalRank` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* N. Wang; L. Chen (2025). *Equality condition for a matrix inequality by partial transpose*. DOI: [10.1142/S1230161226500071](https://doi.org/10.1142/S1230161226500071). URL: <https://arxiv.org/abs/2508.18644v1>.

*Commentary.*

The image dimension of the map sending x to the ordered pair (first(x),second(x)).

**Theorem 1.13 (Duality exchanges horizontal and vertical ranks).**

Lean statement: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.horizontalRank_dual`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.horizontalRank_dual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* N. Wang; L. Chen (2025). *Equality condition for a matrix inequality by partial transpose*. DOI: [10.1142/S1230161226500071](https://doi.org/10.1142/S1230161226500071). URL: <https://arxiv.org/abs/2508.18644v1>.

*Commentary.*

The horizontal rank of the dual pencil equals the vertical rank of the original pencil. The dual of the joint output map is the horizontal pair map after the natural product-dual equivalence.

**Theorem 1.14 (The other pair-rank duality identity).**

Lean statement: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.verticalRank_dual`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.verticalRank_dual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* N. Wang; L. Chen (2025). *Equality condition for a matrix inequality by partial transpose*. DOI: [10.1142/S1230161226500071](https://doi.org/10.1142/S1230161226500071). URL: <https://arxiv.org/abs/2508.18644v1>.

*Commentary.*

The vertical rank of the dual pencil equals the original horizontal rank. Restriction of functionals to the two product inclusions identifies the relevant dual map.

**Theorem 1.15 (Coordinates recover horizontal concatenation rank).**

Lean statement: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.horizontalRank_matrix`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.horizontalRank_matrix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* N. Wang; L. Chen (2025). *Equality condition for a matrix inequality by partial transpose*. DOI: [10.1142/S1230161226500071](https://doi.org/10.1142/S1230161226500071). URL: <https://arxiv.org/abs/2508.18644v1>.

*Commentary.*

In any finite source and target bases, the abstract horizontal pair rank equals the matrix rank of the horizontal concatenation of the two arrow matrices.

**Theorem 1.16 (Coordinates recover vertical concatenation rank).**

Lean statement: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.verticalRank_matrix`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.verticalRank_matrix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* N. Wang; L. Chen (2025). *Equality condition for a matrix inequality by partial transpose*. DOI: [10.1142/S1230161226500071](https://doi.org/10.1142/S1230161226500071). URL: <https://arxiv.org/abs/2508.18644v1>.

*Commentary.*

In any finite source and target bases, the abstract joint output rank equals the matrix rank of the vertical concatenation of the two arrow matrices.

**Theorem 1.17 (Arbitrary bases compute tensor rank).**

Lean statement: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.tensorRank_matrix`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.tensorRank_matrix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* N. Wang; L. Chen (2025). *Equality condition for a matrix inequality by partial transpose*. DOI: [10.1142/S1230161226500071](https://doi.org/10.1142/S1230161226500071). URL: <https://arxiv.org/abs/2508.18644v1>.

*Commentary.*

Choose finite bases independently in both source and both target spaces. The abstract tensor rank equals the rank of the two-term Kronecker sum of the four arrow matrices.

**Theorem 1.18 (A first-factor bidual preserves tensor rank).**

Lean statement: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.tensorRank_dual_dual_left`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.tensorRank_dual_dual_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* N. Wang; L. Chen (2025). *Equality condition for a matrix inequality by partial transpose*. DOI: [10.1142/S1230161226500071](https://doi.org/10.1142/S1230161226500071). URL: <https://arxiv.org/abs/2508.18644v1>.

*Commentary.*

Dualize the first pencil twice. In the two dual bases its arrow matrices are the double transposes of the original arrow matrices, so every tensor rank is unchanged.

**Theorem 1.19 (Exchange of tensor factors preserves rank).**

Lean statement: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.tensorRank_comm`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.tensorRank_comm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* N. Wang; L. Chen (2025). *Equality condition for a matrix inequality by partial transpose*. DOI: [10.1142/S1230161226500071](https://doi.org/10.1142/S1230161226500071). URL: <https://arxiv.org/abs/2508.18644v1>.

*Commentary.*

Exchanging both pencils permutes the product row and column indices. Commutativity of complex scalar multiplication gives equality of tensor ranks.

**Theorem 1.20 (Simultaneous duality transposes the full tensor matrix).**

Lean statement: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.tensorRank_dual_dual`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.tensorRank_dual_dual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* N. Wang; L. Chen (2025). *Equality condition for a matrix inequality by partial transpose*. DOI: [10.1142/S1230161226500071](https://doi.org/10.1142/S1230161226500071). URL: <https://arxiv.org/abs/2508.18644v1>.

*Commentary.*

Dualizing both pencils once transposes their complete tensor matrix in dual bases. Full matrix transposition preserves rank.

**Theorem 1.21 (Partial duality moves between the factors).**

Lean statement: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.tensorRank_dual_left_exchange`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.tensorRank_dual_left_exchange` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* N. Wang; L. Chen (2025). *Equality condition for a matrix inequality by partial transpose*. DOI: [10.1142/S1230161226500071](https://doi.org/10.1142/S1230161226500071). URL: <https://arxiv.org/abs/2508.18644v1>.

*Commentary.*

The tensor rank of the dual first pencil with the unchanged second pencil equals that of the unchanged first pencil with the dual second pencil. Combine simultaneous duality with the bidual identity.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.LeftReduction`
- Truth anchor: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.Pencil`
- Truth anchor: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.RightReduced`
- Truth anchor: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.RightReduction`
- Truth anchor: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.SplitData`
- Truth anchor: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.TwoSidedReduction`
- Truth anchor: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.dual`
- Truth anchor: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.horizontalRank`
- Truth anchor: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.horizontalRank_dual`
- Truth anchor: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.horizontalRank_matrix`
- Truth anchor: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.remainder`
- Truth anchor: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.tensorRank`
- Truth anchor: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.tensorRank_comm`
- Truth anchor: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.tensorRank_dual_dual`
- Truth anchor: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.tensorRank_dual_dual_left`
- Truth anchor: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.tensorRank_dual_left_exchange`
- Truth anchor: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.tensorRank_matrix`
- Truth anchor: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.two_sided_reduction`
- Truth anchor: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.verticalRank`
- Truth anchor: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.verticalRank_dual`
- Truth anchor: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.verticalRank_matrix`
- Dependency: [D5/S3/Quantum/Entanglement/PartialTransposeSaturation/ChainSplitting](ChainSplitting.md)
- Dependency: [D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Sufficiency](Sufficiency.md)
