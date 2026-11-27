# Integral L1 Repair for Totally Unimodular Matrices

## Abstract

Finite totally unimodular integer systems admit integral repairs at the cost of any feasible real solution.

**Definition 1.1 (Nonzero coordinates).**

Lean statement: `D5/S3/HomologicalAlgebra/TotalUnimodularL1Repair.nonzeroSupport`

*Formalization.* `D5/S3/HomologicalAlgebra/TotalUnimodularL1Repair.nonzeroSupport` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Marcia Fampa and Jon Lee (2018). *On Sparse Reflexive Generalized Inverses*. URL: <https://arxiv.org/abs/1807.03074v1>.

*Acknowledgement.* Eduardo D. Sontag (1980). *On Generalized Inverses of Polynomial and Other Matrices*. URL: <https://www.sontaglab.org/FTPDIR/wgi.pdf>.

*Commentary.*

Take the finite set of indices where a vector is nonzero.

**Theorem 1.2 (Membership in the support).**

Lean statement: `D5/S3/HomologicalAlgebra/TotalUnimodularL1Repair.mem_nonzeroSupport`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/TotalUnimodularL1Repair.mem_nonzeroSupport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Marcia Fampa and Jon Lee (2018). *On Sparse Reflexive Generalized Inverses*. URL: <https://arxiv.org/abs/1807.03074v1>.

*Acknowledgement.* Eduardo D. Sontag (1980). *On Generalized Inverses of Polynomial and Other Matrices*. URL: <https://www.sontaglab.org/FTPDIR/wgi.pdf>.

*Commentary.*

A coordinate belongs to this set exactly when its value is nonzero.

**Theorem 1.3 (Signed column doubling).**

Lean statement: `D5/S3/HomologicalAlgebra/TotalUnimodularL1Repair.fromCols_neg_isTotallyUnimodular`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/TotalUnimodularL1Repair.fromCols_neg_isTotallyUnimodular` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Marcia Fampa and Jon Lee (2018). *On Sparse Reflexive Generalized Inverses*. URL: <https://arxiv.org/abs/1807.03074v1>.

*Acknowledgement.* Eduardo D. Sontag (1980). *On Generalized Inverses of Polynomial and Other Matrices*. URL: <https://www.sontaglab.org/FTPDIR/wgi.pdf>.

*Commentary.*

An integer matrix and its negation can be placed side by side while preserving total unimodularity. Each minor of the doubled matrix differs from the corresponding indexed minor by a product of column signs.

**Theorem 1.4 (An integral solution within the real L1 cost).**

Lean statement: `D5/S3/HomologicalAlgebra/TotalUnimodularL1Repair.exists_integer_l1_repair`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/TotalUnimodularL1Repair.exists_integer_l1_repair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Marcia Fampa and Jon Lee (2018). *On Sparse Reflexive Generalized Inverses*. URL: <https://arxiv.org/abs/1807.03074v1>.

*Acknowledgement.* Eduardo D. Sontag (1980). *On Generalized Inverses of Polynomial and Other Matrices*. URL: <https://www.sontaglab.org/FTPDIR/wgi.pdf>.

*Commentary.*

The matrix has finite row and column types and every square minor has determinant zero, one, or minus one. The right-hand side is integral and the given real vector solves the real scalar extension of that same system. The conclusion gives an integer solution whose sum of absolute coordinates is at most the real vector's cost.

Split the real vector into positive and negative parts. A feasible step in a supported kernel direction removes a nonzero coordinate without raising the cost. Once the supporting columns are independent, the integral inner inverse reconstructs the restricted solution. Subtract the two nonnegative integer parts to recover the signed repair.

**Theorem 1.5 (Integer support is bounded by L1 cost).**

Lean statement: `D5/S3/HomologicalAlgebra/TotalUnimodularL1Repair.support_card_le_sum_abs`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/TotalUnimodularL1Repair.support_card_le_sum_abs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Marcia Fampa and Jon Lee (2018). *On Sparse Reflexive Generalized Inverses*. URL: <https://arxiv.org/abs/1807.03074v1>.

*Acknowledgement.* Eduardo D. Sontag (1980). *On Generalized Inverses of Polynomial and Other Matrices*. URL: <https://www.sontaglab.org/FTPDIR/wgi.pdf>.

*Commentary.*

Each nonzero integer coordinate contributes at least one to the sum of absolute values.

**Theorem 1.6 (Reduction of an integer solution).**

Lean statement: `D5/S3/HomologicalAlgebra/TotalUnimodularL1Repair.reduce_integer_solution`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/TotalUnimodularL1Repair.reduce_integer_solution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Marcia Fampa and Jon Lee (2018). *On Sparse Reflexive Generalized Inverses*. URL: <https://arxiv.org/abs/1807.03074v1>.

*Acknowledgement.* Eduardo D. Sontag (1980). *On Generalized Inverses of Polynomial and Other Matrices*. URL: <https://www.sontaglab.org/FTPDIR/wgi.pdf>.

*Commentary.*

For each natural number n, reduction in ZMod n carries the integer matrix equation to the reduced system. The support of the reduced vector is contained in the integer support.

**Theorem 1.7 (Modular repair from a real solution).**

Lean statement: `D5/S3/HomologicalAlgebra/TotalUnimodularL1Repair.exists_zmod_repair_with_support_bound`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/TotalUnimodularL1Repair.exists_zmod_repair_with_support_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Marcia Fampa and Jon Lee (2018). *On Sparse Reflexive Generalized Inverses*. URL: <https://arxiv.org/abs/1807.03074v1>.

*Acknowledgement.* Eduardo D. Sontag (1980). *On Generalized Inverses of Polynomial and Other Matrices*. URL: <https://www.sontaglab.org/FTPDIR/wgi.pdf>.

*Commentary.*

For a totally unimodular integer matrix and a feasible real solution with integral right-hand side, the cardinality of the repair's support over ZMod n is bounded by the real L1 cost.

The integral-feasibility principle is classical. Hoffman and Kruskal's Integral Boundary Points of Convex Polyhedra (1956) gives the polyhedral integrality background. The Lean construction uses the repository's IntegerMatrixInnerInverse theorem and its selected-minor and splitting antecedents in Fampa and Lee and in Sontag.

## References

- Truth anchor: `D5/S3/HomologicalAlgebra/TotalUnimodularL1Repair.exists_integer_l1_repair`
- Truth anchor: `D5/S3/HomologicalAlgebra/TotalUnimodularL1Repair.exists_zmod_repair_with_support_bound`
- Truth anchor: `D5/S3/HomologicalAlgebra/TotalUnimodularL1Repair.fromCols_neg_isTotallyUnimodular`
- Truth anchor: `D5/S3/HomologicalAlgebra/TotalUnimodularL1Repair.mem_nonzeroSupport`
- Truth anchor: `D5/S3/HomologicalAlgebra/TotalUnimodularL1Repair.nonzeroSupport`
- Truth anchor: `D5/S3/HomologicalAlgebra/TotalUnimodularL1Repair.reduce_integer_solution`
- Truth anchor: `D5/S3/HomologicalAlgebra/TotalUnimodularL1Repair.support_card_le_sum_abs`
- Dependency: [D5/S3/HomologicalAlgebra/IntegerMatrixInnerInverse](IntegerMatrixInnerInverse.md)
