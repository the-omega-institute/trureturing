# The Jacobi parity dissection

## Abstract

A parity bijection dissects the complete product U(q)U(q³).

The three factors use the weighted Jacobi specialization, a sign twist on the Laurent support cone, and constant-unit evaluation. For the product U(q)U(q³), write the starting integer indices as a and b. The two affine coordinates come from a+3b and a−b divided by two. Folding one coordinate in each parity case gives the two disjoint lattices. The bijection preserves the degrees and turns the original signs into a positive even summand and a negative odd summand. The contributing index pairs at each fixed degree lie in a finite set.

**Definition 1.1 (U).**

Lean statement: `D5/S3/Arith/ModularForms/DesignatedSummandThetaDissection.U`

*Formalization.* `D5/S3/Arith/ModularForms/DesignatedSummandThetaDissection.U` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Daniel Yaqubi and Madjid Mirzavaziri (2026). *Partitions with designated summands: k-tuples and their congruences*. DOI: [10.48550/arXiv.2611.05623](https://doi.org/10.48550/arXiv.2611.05623). URL: <https://arxiv.org/abs/2611.05623v1>.

*Commentary.*

The signed weighted Jacobi sum at weight parameters 2 and 1.

**Definition 1.2 (phi).**

Lean statement: `D5/S3/Arith/ModularForms/DesignatedSummandThetaDissection.phi`

*Formalization.* `D5/S3/Arith/ModularForms/DesignatedSummandThetaDissection.phi` (`✓ std3`).

*Citation.* Daniel Yaqubi and Madjid Mirzavaziri (2026). *Partitions with designated summands: k-tuples and their congruences*. DOI: [10.48550/arXiv.2611.05623](https://doi.org/10.48550/arXiv.2611.05623). URL: <https://arxiv.org/abs/2611.05623v1>.

*Commentary.*

The bilateral theta series with square exponents.

**Definition 1.3 (psi).**

Lean statement: `D5/S3/Arith/ModularForms/DesignatedSummandThetaDissection.psi`

*Formalization.* `D5/S3/Arith/ModularForms/DesignatedSummandThetaDissection.psi` (`✓ std3`).

*Citation.* Daniel Yaqubi and Madjid Mirzavaziri (2026). *Partitions with designated summands: k-tuples and their congruences*. DOI: [10.48550/arXiv.2611.05623](https://doi.org/10.48550/arXiv.2611.05623). URL: <https://arxiv.org/abs/2611.05623v1>.

*Commentary.*

The unilateral theta series with triangular exponents.

**Theorem 1.4 (U_product).**

Lean statement: `D5/S3/Arith/ModularForms/DesignatedSummandThetaDissection.U_product`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/DesignatedSummandThetaDissection.U_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Yaqubi and Madjid Mirzavaziri (2026). *Partitions with designated summands: k-tuples and their congruences*. DOI: [10.48550/arXiv.2611.05623](https://doi.org/10.48550/arXiv.2611.05623). URL: <https://arxiv.org/abs/2611.05623v1>.

*Commentary.*

The series U times the Euler factor f2 is f4 f1.

**Theorem 1.5 (phi_product).**

Lean statement: `D5/S3/Arith/ModularForms/DesignatedSummandThetaDissection.phi_product`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/DesignatedSummandThetaDissection.phi_product` (`✓ std3`). ∎

*Citation.* Daniel Yaqubi and Madjid Mirzavaziri (2026). *Partitions with designated summands: k-tuples and their congruences*. DOI: [10.48550/arXiv.2611.05623](https://doi.org/10.48550/arXiv.2611.05623). URL: <https://arxiv.org/abs/2611.05623v1>.

*Commentary.*

The series phi times f1 squared and f4 squared is f2 to the fifth power.

**Theorem 1.6 (psi_product).**

Lean statement: `D5/S3/Arith/ModularForms/DesignatedSummandThetaDissection.psi_product`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/DesignatedSummandThetaDissection.psi_product` (`✓ std3`). ∎

*Citation.* Daniel Yaqubi and Madjid Mirzavaziri (2026). *Partitions with designated summands: k-tuples and their congruences*. DOI: [10.48550/arXiv.2611.05623](https://doi.org/10.48550/arXiv.2611.05623). URL: <https://arxiv.org/abs/2611.05623v1>.

*Commentary.*

The series psi times f1 is f2 squared.

**Theorem 1.7 (U_dissection).**

Lean statement: `D5/S3/Arith/ModularForms/DesignatedSummandThetaDissection.U_dissection`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/DesignatedSummandThetaDissection.U_dissection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Yaqubi and Madjid Mirzavaziri (2026). *Partitions with designated summands: k-tuples and their congruences*. DOI: [10.48550/arXiv.2611.05623](https://doi.org/10.48550/arXiv.2611.05623). URL: <https://arxiv.org/abs/2611.05623v1>.

*Commentary.*

The two summands are psi(q⁴) phi(q⁶) and minus q times phi(q²) psi(q¹²).

## References

- Truth anchor: `D5/S3/Arith/ModularForms/DesignatedSummandThetaDissection.U`
- Truth anchor: `D5/S3/Arith/ModularForms/DesignatedSummandThetaDissection.U_dissection`
- Truth anchor: `D5/S3/Arith/ModularForms/DesignatedSummandThetaDissection.U_product`
- Truth anchor: `D5/S3/Arith/ModularForms/DesignatedSummandThetaDissection.phi`
- Truth anchor: `D5/S3/Arith/ModularForms/DesignatedSummandThetaDissection.phi_product`
- Truth anchor: `D5/S3/Arith/ModularForms/DesignatedSummandThetaDissection.psi`
- Truth anchor: `D5/S3/Arith/ModularForms/DesignatedSummandThetaDissection.psi_product`
- Dependency: [D5/S3/Arith/ModularForms/CubicThetaTwistedColumns](CubicThetaTwistedColumns.md)
- Dependency: [D5/S3/Arith/ModularForms/WeightedJacobiSpecialization](WeightedJacobiSpecialization.md)
- Dependency: [D5/S3/Combinatorics/PowerSeries/DilatedEulerProduct](../../Combinatorics/PowerSeries/DilatedEulerProduct.md)
