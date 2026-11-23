# The Jacobi parity dissection

## Abstract

A parity bijection dissects the complete product U(q)U(q³).

The three factors use the weighted Jacobi specialization, a sign twist on the Laurent support cone, and constant-unit evaluation. For the product U(q)U(q³), write the starting integer indices as a and b. The two affine coordinates come from a+3b and a−b divided by two. Folding one coordinate in each parity case gives the two disjoint lattices. The bijection preserves the degrees and turns the original signs into a positive even summand and a negative odd summand. The contributing index pairs at each fixed degree lie in a finite set.

**Theorem 1.1 (prod_split_two).**

Lean statement: `D5/S3/Arith/ModularForms/DesignatedSummandThetaDissection.prod_split_two`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/DesignatedSummandThetaDissection.prod_split_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Yaqubi and Madjid Mirzavaziri (2026). *Partitions with designated summands: k-tuples and their congruences*. DOI: [10.48550/arXiv.2611.05623](https://doi.org/10.48550/arXiv.2611.05623). URL: <https://arxiv.org/abs/2611.05623v1>.

*Commentary.*

A product through 2N consecutive indices is the product through the N even and the N odd indices.

**Definition 1.2 (U).**

$$U : \operatorname{PowerSeries}\left(\mathbb{Q}\right) := \operatorname{J}\left(2, 1\right) = \sum_{j \in \mathbb{Z}} (-1)^{\lvert j\rvert}\,q^{2j^{2} - j}$$

*Formalization.* `D5/S3/Arith/ModularForms/DesignatedSummandThetaDissection.U` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Daniel Yaqubi and Madjid Mirzavaziri (2026). *Partitions with designated summands: k-tuples and their congruences*. DOI: [10.48550/arXiv.2611.05623](https://doi.org/10.48550/arXiv.2611.05623). URL: <https://arxiv.org/abs/2611.05623v1>.

*Commentary.*

The signed weighted Jacobi sum J at weight parameters 2 and 1, as a rational formal power series. In all three series q is the formal indeterminate.

**Definition 1.3 (phi).**

$$\varphi : \operatorname{PowerSeries}\left(\mathbb{Q}\right) := \operatorname{specialize}\left(0, 1, \operatorname{map}\left(\operatorname{twist}\left(id, -1\right), jacobiSeries\right)\right) = \sum_{j \in \mathbb{Z}} q^{j^{2}}$$

*Formalization.* `D5/S3/Arith/ModularForms/DesignatedSummandThetaDissection.phi` (`✓ std3`).

*Citation.* Daniel Yaqubi and Madjid Mirzavaziri (2026). *Partitions with designated summands: k-tuples and their congruences*. DOI: [10.48550/arXiv.2611.05623](https://doi.org/10.48550/arXiv.2611.05623). URL: <https://arxiv.org/abs/2611.05623v1>.

*Commentary.*

The bilateral theta series with square exponents. The defining specialization at weights 0 and 1 follows the Laurent twist with the unit −1 of the rationals and the identity ring homomorphism on the rational coefficients.

**Definition 1.4 (psi).**

$$\psi : \operatorname{PowerSeries}\left(\mathbb{Q}\right) := \operatorname{C}\left(\frac{1}{2}\right)\,\operatorname{jacobiEvaluation}\left(id, -1\right) = \sum_{j \in \mathbb{N}} q^{\frac{j(j+1)}{2}}$$

*Formalization.* `D5/S3/Arith/ModularForms/DesignatedSummandThetaDissection.psi` (`✓ std3`).

*Citation.* Daniel Yaqubi and Madjid Mirzavaziri (2026). *Partitions with designated summands: k-tuples and their congruences*. DOI: [10.48550/arXiv.2611.05623](https://doi.org/10.48550/arXiv.2611.05623). URL: <https://arxiv.org/abs/2611.05623v1>.

*Commentary.*

The unilateral theta series with triangular exponents. The defining Jacobi evaluation uses the identity ring homomorphism on the rational coefficients and the rational unit −1. C embeds the rational number one half as a constant series.

**Theorem 1.5 (U_product).**

Lean statement: `D5/S3/Arith/ModularForms/DesignatedSummandThetaDissection.U_product`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/DesignatedSummandThetaDissection.U_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Yaqubi and Madjid Mirzavaziri (2026). *Partitions with designated summands: k-tuples and their congruences*. DOI: [10.48550/arXiv.2611.05623](https://doi.org/10.48550/arXiv.2611.05623). URL: <https://arxiv.org/abs/2611.05623v1>.

*Commentary.*

The series U times the Euler factor f2 is f4 f1.

**Theorem 1.6 (phi_product).**

Lean statement: `D5/S3/Arith/ModularForms/DesignatedSummandThetaDissection.phi_product`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/DesignatedSummandThetaDissection.phi_product` (`✓ std3`). ∎

*Citation.* Daniel Yaqubi and Madjid Mirzavaziri (2026). *Partitions with designated summands: k-tuples and their congruences*. DOI: [10.48550/arXiv.2611.05623](https://doi.org/10.48550/arXiv.2611.05623). URL: <https://arxiv.org/abs/2611.05623v1>.

*Commentary.*

The series phi times f1 squared and f4 squared is f2 to the fifth power.

**Theorem 1.7 (psi_product).**

Lean statement: `D5/S3/Arith/ModularForms/DesignatedSummandThetaDissection.psi_product`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/DesignatedSummandThetaDissection.psi_product` (`✓ std3`). ∎

*Citation.* Daniel Yaqubi and Madjid Mirzavaziri (2026). *Partitions with designated summands: k-tuples and their congruences*. DOI: [10.48550/arXiv.2611.05623](https://doi.org/10.48550/arXiv.2611.05623). URL: <https://arxiv.org/abs/2611.05623v1>.

*Commentary.*

The series psi times f1 is f2 squared.

**Theorem 1.8 (U_dissection).**

Lean statement: `D5/S3/Arith/ModularForms/DesignatedSummandThetaDissection.U_dissection`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/DesignatedSummandThetaDissection.U_dissection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Yaqubi and Madjid Mirzavaziri (2026). *Partitions with designated summands: k-tuples and their congruences*. DOI: [10.48550/arXiv.2611.05623](https://doi.org/10.48550/arXiv.2611.05623). URL: <https://arxiv.org/abs/2611.05623v1>.

*Commentary.*

Over the rationals, U(q) U(q³) equals psi(q⁴) phi(q⁶) minus q phi(q²) psi(q¹²).

## References

- Truth anchor: `D5/S3/Arith/ModularForms/DesignatedSummandThetaDissection.U`
- Truth anchor: `D5/S3/Arith/ModularForms/DesignatedSummandThetaDissection.U_dissection`
- Truth anchor: `D5/S3/Arith/ModularForms/DesignatedSummandThetaDissection.U_product`
- Truth anchor: `D5/S3/Arith/ModularForms/DesignatedSummandThetaDissection.phi`
- Truth anchor: `D5/S3/Arith/ModularForms/DesignatedSummandThetaDissection.phi_product`
- Truth anchor: `D5/S3/Arith/ModularForms/DesignatedSummandThetaDissection.prod_split_two`
- Truth anchor: `D5/S3/Arith/ModularForms/DesignatedSummandThetaDissection.psi`
- Truth anchor: `D5/S3/Arith/ModularForms/DesignatedSummandThetaDissection.psi_product`
- Dependency: [D5/S3/Arith/ModularForms/CubicThetaTwistedColumns](CubicThetaTwistedColumns.md)
- Dependency: [D5/S3/Arith/ModularForms/WeightedJacobiSpecialization](WeightedJacobiSpecialization.md)
- Dependency: [D5/S3/Combinatorics/Partitions/DesignatedSummands](../../Combinatorics/Partitions/DesignatedSummands.md)
