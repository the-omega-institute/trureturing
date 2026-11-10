# Literal lattice Zhu source relations

## Abstract

ActualZhuGroundCurrent

The native carrier is the complete finite-support sum over integral lattice charges of the complex oscillator polynomial algebra. O is the original literal span of circles with unrestricted second state. Positive definiteness is the sole extra lattice hypothesis for quotient multiplication. No restriction to nonzero rank, nonzero charge, a preferred dual class or a unique minimum is imposed.

Dong, Li and Mason, Certain associative algebras similar to U(sl2) and Zhu's algebra A(V_L), DOI 10.1006/jabr.1997.7112, arXiv q-alg/9605032v1, Theorem 3.4 and Remark 2.11, supply the classical lattice Zhu framework. The native fields, grading, creation and translation retain their original definitions. The quotient product and literal circle relations use the original binomial coefficient choose(m,i).

ActualZhuProduct and ActualZhuAlgebra supply the original star and quotient product; the native derivative, creation and mixed-current identities compute the ground right-current law. ActualZhuOscillator and ActualZhuCurrentNormalForm use these identities to reduce every oscillator polynomial, and ActualZhuSourceSupport applies the translation relation to charged ground states.

**Theorem 1.1 (Ground energy).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/ActualZhuGroundCurrent.ground_grade`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/ActualZhuGroundCurrent.ground_grade` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every original ground state has its nonnegative integral half-norm energy.

**Theorem 1.2 (Translation and weight).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/ActualZhuGroundCurrent.translation_weight_mem_zhuO`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/ActualZhuGroundCurrent.translation_weight_mem_zhuO` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any homogeneous original state a of natural weight K, T(a)+K a lies in the same literal O.

**Theorem 1.3 (Direct ground right-current law).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/ActualZhuGroundCurrent.ground_right_current`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/ActualZhuGroundCurrent.ground_right_current` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The mixed commutator at current mode -1, creation and creativity give E_delta H_i equal to the class of h_i(-1)e_delta. The zero-weight star row is handled separately.

**Theorem 1.4 (Current energy).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/ActualZhuGroundCurrent.current_grade`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/ActualZhuGroundCurrent.current_grade` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original current state is homogeneous of energy one.

**Theorem 1.5 (Left current on a full sector).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/ActualZhuGroundCurrent.current_star_single`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/ActualZhuGroundCurrent.current_star_single` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every oscillator polynomial p, H_i pi(single(delta,p)) is pi(single(delta,X(i,0)p)) plus B(e_i,delta) pi(single(delta,p)).

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/ActualZhuGroundCurrent.current_grade`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/ActualZhuGroundCurrent.current_star_single`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/ActualZhuGroundCurrent.ground_grade`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/ActualZhuGroundCurrent.ground_right_current`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/ActualZhuGroundCurrent.translation_weight_mem_zhuO`
- Dependency: [D5/S3/VertexAlgebra/Lattice/ActualZhuAlgebra](ActualZhuAlgebra.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeActualConformalState](../LatticeActualConformalState.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeActualMixedLocality](../LatticeActualMixedLocality.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeActualVertexAlgebra](../LatticeActualVertexAlgebra.md)
