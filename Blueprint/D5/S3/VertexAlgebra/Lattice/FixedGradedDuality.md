# Fixed-grade nondegeneracy and the algebraic restricted dual

## Abstract

Conditional fixed-energy graded duality on the original Carrier

The construction uses the original Carrier D, its literal FixedCarrier D, and the existing grade D h. The fixed grade is the comap of grade D h along the FixedCarrier inclusion. No alternate carrier and no live P1 pairing are introduced.

The ambient bilinear form B is an explicit parameter. The assumptions are ambient left and right nondegeneracy, theta isometry, commutation of theta with the existing grade projection, and orthogonality of distinct grades. The fixed-grade witness is plusPart D (gradeProjection h y): projection is recovered by the existing finite grade decomposition, then theta averaging supplies fixed-space membership.

With the existing positive-Gram finite-grade supplier, every fixed grade is finite-dimensional. The proved restriction is nondegenerate in both slots, so BilinForm.toDual gives the actual grade dual equivalence. The dependent direct sum of these algebraic duals and its evaluation through the genuine fixed-energy decomposition are defined explicitly.

This is a conditional algebraic supplier. It does not instantiate the live P1 pairing, prove module equivariance, all-source BPZ, Hilbert or analytic CFT, fusion, full string theory, anomaly cancellation, or AdS-CFT.

**Definition 1.1 (FixedGrade).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.FixedGrade`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.FixedGrade` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual fixed grade, represented as grade D h comapped along the subtype inclusion into FixedCarrier D.

**Definition 1.2 (fixedGradeSubmodule).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.fixedGradeSubmodule`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.fixedGradeSubmodule` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed-grade submodule of FixedCarrier D.

**Definition 1.3 (fixedGradeToCarrier).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.fixedGradeToCarrier`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.fixedGradeToCarrier` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The inclusion of a fixed grade into the original Carrier D.

**Definition 1.4 (fixedGradeForm).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.fixedGradeForm`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.fixedGradeForm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The restriction of the explicit ambient bilinear form to the actual fixed grade.

**Theorem 1.5 (fixedGradeForm_apply).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.fixedGradeForm_apply`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.fixedGradeForm_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Evaluation of the restricted form is ambient B on the original Carrier inclusions.

**Theorem 1.6 (fixedGradeProjection_mem).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.fixedGradeProjection_mem`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.fixedGradeProjection_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A projected fixed vector remains in the actual fixed space under the explicit grade-commutation hypothesis.

**Definition 1.7 (fixedGradeProjection).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.fixedGradeProjection`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.fixedGradeProjection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual projection from FixedCarrier D to its fixed grade h.

**Theorem 1.8 (fixedGradeProjection_sum).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.fixedGradeProjection_sum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.fixedGradeProjection_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite stateEnergies support and existing sum_gradeProjections reconstruct every FixedCarrier vector.

**Theorem 1.9 (fixedGrades_independent).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.fixedGrades_independent`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.fixedGrades_independent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Distinct actual fixed grades are internally independent by the existing grade independence.

**Theorem 1.10 (fixedGrades_iSup).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.fixedGrades_iSup`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.fixedGrades_iSup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual fixed grades span FixedCarrier D using the existing finite decomposition and grade stability.

**Definition 1.11 (fixedEnergyDecomposition).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.fixedEnergyDecomposition`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.fixedEnergyDecomposition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The genuine linear equivalence between FixedCarrier D and the dependent direct sum of all actual fixed grades.

**Theorem 1.12 (fixedGrade_finiteDimensional).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.fixedGrade_finiteDimensional`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.fixedGrade_finiteDimensional` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positive Gram supplies finite-dimensionality of every actual fixed grade.

**Definition 1.13 (fixedGradeWitness).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.fixedGradeWitness`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.fixedGradeWitness` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit projected and theta-averaged ambient witness in the actual fixed grade.

**Theorem 1.14 (fixedGrade_dualEquiv).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.fixedGrade_dualEquiv`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.fixedGrade_dualEquiv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Ambient nondegeneracy, theta isometry, grade stability and grade orthogonality imply genuine fixed-grade nondegeneracy and the finite-grade algebraic dual equivalence.

**Definition 1.15 (fixedGradeNondegenerate).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.fixedGradeNondegenerate`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.fixedGradeNondegenerate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The selected nondegeneracy proof obtained from the explicit ambient witness construction.

**Definition 1.16 (fixedGradeDualEquiv).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.fixedGradeDualEquiv`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.fixedGradeDualEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual finite-grade equivalence to the full algebraic dual, built from the restricted form and its proved nondegeneracy.

**Theorem 1.17 (fixedGradeDualEquiv_evaluation).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.fixedGradeDualEquiv_evaluation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.fixedGradeDualEquiv_evaluation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The selected finite-grade dual equivalence evaluates to the restricted ambient form on every fixed grade.

**Theorem 1.18 (fixedGradeDualEquiv_ambient_evaluation).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.fixedGradeDualEquiv_ambient_evaluation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.fixedGradeDualEquiv_ambient_evaluation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The selected finite-grade dual equivalence evaluates to the original ambient bilinear form on the original Carrier inclusions.

**Definition 1.19 (FixedRestrictedDual).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.FixedRestrictedDual`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.FixedRestrictedDual` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The dependent direct sum of the full algebraic duals of all actual fixed grades.

**Definition 1.20 (fixedRestrictedDualEvaluation).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.fixedRestrictedDualEvaluation`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.fixedRestrictedDualEvaluation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Evaluation of an algebraic restricted-dual vector through the genuine fixed-energy decomposition.

**Definition 1.21 (fixedRestrictedDualEquiv).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.fixedRestrictedDualEquiv`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.fixedRestrictedDualEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual algebraic graded restricted-dual equivalence assembled from the finite-grade equivalences and the fixed-energy decomposition.

**Theorem 1.22 (fixedGrade_dual_evaluation).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.fixedGrade_dual_evaluation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.fixedGrade_dual_evaluation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The restricted form evaluates the inverse of toDual exactly as the given grade functional.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.FixedGrade`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.FixedRestrictedDual`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.fixedEnergyDecomposition`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.fixedGradeDualEquiv`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.fixedGradeDualEquiv_ambient_evaluation`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.fixedGradeDualEquiv_evaluation`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.fixedGradeForm`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.fixedGradeForm_apply`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.fixedGradeNondegenerate`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.fixedGradeProjection`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.fixedGradeProjection_mem`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.fixedGradeProjection_sum`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.fixedGradeSubmodule`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.fixedGradeToCarrier`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.fixedGradeWitness`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.fixedGrade_dualEquiv`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.fixedGrade_dual_evaluation`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.fixedGrade_finiteDimensional`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.fixedGrades_iSup`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.fixedGrades_independent`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.fixedRestrictedDualEquiv`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FixedGradedDuality.fixedRestrictedDualEvaluation`
- Dependency: [D5/S3/VertexAlgebra/LatticeEnergyGrading](../LatticeEnergyGrading.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeInvolution](../LatticeInvolution.md)
