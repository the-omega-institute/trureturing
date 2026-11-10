# Literal lattice Zhu source relations

## Abstract

ActualZhuCurrentRelations

The native carrier is the complete finite-support sum over integral lattice charges of the complex oscillator polynomial algebra. O is the original literal span of circles with unrestricted second state. Positive definiteness is the sole extra lattice hypothesis for quotient multiplication. No restriction to nonzero rank, nonzero charge, a preferred dual class or a unique minimum is imposed.

Dong, Li and Mason, Certain associative algebras similar to U(sl2) and Zhu's algebra A(V_L), DOI 10.1006/jabr.1997.7112, arXiv q-alg/9605032v1, Theorem 3.4 and Remark 2.11, supply the classical lattice Zhu framework. The native fields, grading, creation and translation retain their original definitions. The quotient product and literal circle relations use the original binomial coefficient choose(m,i).

ActualZhuCurrentNormalForm, the native creation derivative and ground-product coefficients identify full opposite-charge circles with falling-factorial current polynomials. ActualZhuSourceProjectors applies the resulting relation for every integral alpha to eliminate grid weights violating a lattice inequality.

**Theorem 1.1 (Weighted energy).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentRelations.single_weighted_grade`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentRelations.single_weighted_grade` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Weighted oscillator homogeneity gives the exact original charge-plus-oscillator grade.

**Definition 1.2 (Charge-linear current).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentRelations.Hcharge`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentRelations.Hcharge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

H_alpha is the sum of alpha_i H_i; this includes rank zero.

**Theorem 1.3 (Neutral creation recurrence).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentRelations.creation_class_recurrence`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentRelations.creation_class_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Translation of the original creation coefficient and its exact energy give (n+1) C_(n+1)=(H_alpha-n) C_n in the literal quotient. The original creation_derivation proof is reused.

**Theorem 1.4 (Falling-factorial coefficients).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentRelations.creation_class_choose`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentRelations.creation_class_choose` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The neutral creation coefficient class is Ring.choose(H_alpha,n), by the exact recurrence and initial value.

**Theorem 1.5 (Full opposite-charge circle).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentRelations.opposite_circle_sum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentRelations.opposite_circle_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original ground_product supplier evaluates the literal circle of e_alpha with e_(-alpha), retaining all choose(k,j) terms.

**Theorem 1.6 (Chu-Vandermonde relation).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentRelations.current_choose_relation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentRelations.current_choose_relation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete opposite-circle sum is Ring.choose(k+H_alpha,2k+1), which vanishes in the source quotient.

**Theorem 1.7 (All-alpha squarefree current polynomial).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentRelations.all_alpha_current_relation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentRelations.all_alpha_current_relation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every alpha, the ordered product over j=0,...,2k of H_alpha+k-j vanishes, where k is its nonnegative charge energy. The factors have the distinct integer roots -k,...,k. Alpha zero and rank zero are included; rationality and semisimplicity are not assumed.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentRelations.Hcharge`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentRelations.all_alpha_current_relation`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentRelations.creation_class_choose`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentRelations.creation_class_recurrence`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentRelations.current_choose_relation`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentRelations.opposite_circle_sum`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentRelations.single_weighted_grade`
- Dependency: [D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentNormalForm](ActualZhuCurrentNormalForm.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/NormFourFixedPeirce](NormFourFixedPeirce.md)
