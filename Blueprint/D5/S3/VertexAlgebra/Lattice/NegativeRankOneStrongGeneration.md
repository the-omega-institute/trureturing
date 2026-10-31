# Negative Rank-One Outer-Insertion Obstruction

## Abstract

Actual all-state outer-insertion obstruction for negative rank one.

The actual all-state coefficient map preserves the original integer energy grading. The groundCoefficient projection extracts the oscillator-constant coefficient in one charge sector.

**Theorem 1.1 (Ground coefficient vanishes under an exact grade mismatch).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/NegativeRankOneStrongGeneration.groundCoefficient_mode_eq_zero_of_grade_mismatch`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/NegativeRankOneStrongGeneration.groundCoefficient_mode_eq_zero_of_grade_mismatch` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For arbitrary actual states, arbitrary oscillator mixtures, and arbitrary finite charge support, actual_mode_grade forces the fixed charge/constant coefficient to vanish whenever its target energy differs from the mode grade.

**Theorem 1.2 (Negative rank-one outer energy mismatch).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/NegativeRankOneStrongGeneration.negative_rank_one_outer_energy_mismatch`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/NegativeRankOneStrongGeneration.negative_rank_one_outer_energy_mismatch` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For d>0, positive charges s<q, nonnegative oscillator degrees r,t, and a strictly negative mode k, the equality required for a nonzero oscillator-constant output is impossible: r+t+2*d*s*(q-s)-k-1 is strictly positive.

**Theorem 1.3 (Actual all-state outer insertion vanishes).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/NegativeRankOneStrongGeneration.negative_rank_one_outer_insertion_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/NegativeRankOneStrongGeneration.negative_rank_one_outer_insertion_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Combining the exact actual grading with the arithmetic obstruction gives the single-insertion vanishing used by the bounded-charge projection argument. This increment does not assert the unproved arbitrary-word reordering closure.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/NegativeRankOneStrongGeneration.groundCoefficient_mode_eq_zero_of_grade_mismatch`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/NegativeRankOneStrongGeneration.negative_rank_one_outer_energy_mismatch`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/NegativeRankOneStrongGeneration.negative_rank_one_outer_insertion_zero`
- Dependency: [D5/S3/VertexAlgebra/Energy/LatticeCoefficientEnergy](../Energy/LatticeCoefficientEnergy.md)
- Dependency: [D5/S3/VertexAlgebra/Sectors/LatticeSectorIntertwiner](../Sectors/LatticeSectorIntertwiner.md)
