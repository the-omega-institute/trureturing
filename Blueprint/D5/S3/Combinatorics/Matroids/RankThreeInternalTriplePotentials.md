# Ternary Potentials After Adding Internal Triples

## Abstract

Keep the zero-sum mixed triples on the product of a nonzero-dimensional ternary coordinate space and a finite cyclic group. Allow additional triples within each row.

**Theorem 1.1 (A row functional and one shared cyclic map).**

Lean statement: `D5/S3/Combinatorics/Matroids/RankThreeInternalTriplePotentials.potential_iff_separated`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/RankThreeInternalTriplePotentials.potential_iff_separated` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every normalized potential is the sum of a linear functional of the row and a common additive map of the cyclic coordinate. The additive map must vanish on every cyclic difference of uncovered same-row pairs and on every cyclic-coordinate sum of an internal triple. These two conditions suffice. The mixed-triple equation on an affine line identifies the centered functions on two rows and forces additivity. Negation symmetry and characteristic three give the global zero sum for every separated potential.

**Theorem 1.2 (The extra dimension is controlled by the internal residues).**

Lean statement: `D5/S3/Combinatorics/Matroids/RankThreeInternalTriplePotentials.potential_finrank_internal_triples`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/RankThreeInternalTriplePotentials.potential_finrank_internal_triples` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The dimension equals the row dimension plus one exactly when the cyclic group order is divisible by three and all the internal differences and sums reduce to zero modulo three. Otherwise it equals the row dimension. The common additive map is determined by its value at one. Evaluation at zero in the cyclic coordinate recovers the row functional, and evaluation at one in the zero row recovers the allowed cyclic coefficient.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/RankThreeInternalTriplePotentials.potential_finrank_internal_triples`
- Truth anchor: `D5/S3/Combinatorics/Matroids/RankThreeInternalTriplePotentials.potential_iff_separated`
- Dependency: [D5/S3/Combinatorics/Matroids/RankThreeOmissionPotentialFibers](RankThreeOmissionPotentialFibers.md)
