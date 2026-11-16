# Regularity

## Abstract

Regular pencils and partial transpose rank

A square complex pencil with no polynomial kernel chain has an invertible scalar combination. If its determinant polynomial vanished, an integral-domain matrix kernel theorem would give a nonzero polynomial kernel vector. Choose the largest degree among its nonzero coordinates. Taking coefficients gives a finite chain with nonzero final coefficient, contradicting the absence of such chains. A nonzero complex determinant polynomial has a nonzero scalar value.

For a complex endomorphism, generalized eigenspaces split into nilpotent Jordan chains. Reversing each chain defines a nondegenerate bilinear pairing making the endomorphism self-adjoint. In matrix coordinates this gives an invertible intertwiner between a matrix and its transpose. Normalizing a regular pair by an invertible scalar combination therefore gives a simultaneous equivalence between both arrows and their transposes. These are constructive steps of the present proof. Classical matrix-pencil decomposition is a precedent, while the finite chain extraction and its splitting are proved directly.

**Theorem 1.1 (Duality preserves the regular part's tensor rank).**

Lean statement: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Regularity.tensor_rank_dual_eq_of_reduced`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Regularity.tensor_rank_dual_eq_of_reduced` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* N. Wang; L. Chen (2025). *Equality condition for a matrix inequality by partial transpose*. DOI: [10.1142/S1230161226500071](https://doi.org/10.1142/S1230161226500071). URL: <https://arxiv.org/abs/2508.18644v1>.

*Commentary.*

Choose equally indexed finite bases for the square first pair and arbitrary finite bases for the second pair. Dual bases identify dual maps with transposed matrices. The simultaneous transpose equivalence preserves the two-term tensor rank. No independence assumption is needed for the second pair in this equality.

**Theorem 1.2 (A positive-dimensional regular part has positive tensor rank).**

Lean statement: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Regularity.tensor_rank_pos_of_reduced`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Regularity.tensor_rank_pos_of_reduced` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* N. Wang; L. Chen (2025). *Equality condition for a matrix inequality by partial transpose*. DOI: [10.1142/S1230161226500071](https://doi.org/10.1142/S1230161226500071). URL: <https://arxiv.org/abs/2508.18644v1>.

*Commentary.*

A bijective scalar combination on a positive-dimensional source rules out both arrows being zero. If the other pair is linearly independent, its tensor sum with this nonzero pair cannot vanish: in finite bases, exchange the two tensor coordinates and use coefficient independence. The tensor range is therefore nonzero and its finite rank is strictly positive.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Regularity.tensor_rank_dual_eq_of_reduced`
- Truth anchor: `D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Regularity.tensor_rank_pos_of_reduced`
- Dependency: [D5/S1/Eigenstructure/NilpotentJordanChains](../../../../S1/Eigenstructure/NilpotentJordanChains.md)
- Dependency: [D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition](Decomposition.md)
- Dependency: [D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Sufficiency](Sufficiency.md)
