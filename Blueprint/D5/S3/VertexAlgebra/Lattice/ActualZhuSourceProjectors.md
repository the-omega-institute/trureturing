# Finite projectors inside the literal source quotient

## Abstract

ActualZhuSourceProjectors

The carrier and literal circle span are unchanged. The lattice is arbitrary positive-definite integral even, including rank zero and zero charge. Mature source: Dong, Li and Mason, Certain associative algebras similar to U(sl2) and Zhu's algebra A(V_L), DOI 10.1006/jabr.1997.7112, https://arxiv.org/html/q-alg/9605032v1, Theorem 3.4 and Remark 2.11. Native energy, oscillator, source support and inverse Gram suppliers are reused. Lagrange interpolation is supplied by pinned Mathlib under Apache-2.0. These are components of the finite source-span and joint-faithfulness consumer; no independent mathematical novelty or physical completion is asserted.

**Theorem 1.1 (Coordinate interpolation partitions the unit).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/ActualZhuSourceProjectors.coordinate_sum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/ActualZhuSourceProjectors.coordinate_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For coordinate i the native all-alpha relation supplies the nodal polynomial with integer roots from minus k_i through k_i. Pinned Mathlib Lagrange basis polynomials, evaluated in the commutative current subalgebra, sum to one.

**Theorem 1.2 (Coordinate eigenvalue identity).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/ActualZhuSourceProjectors.coordinate_eigen`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/ActualZhuSourceProjectors.coordinate_eigen` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplication by H_i on each coordinate Lagrange factor is its integer node times that factor, because the remaining nodal term vanishes in the literal quotient.

**Theorem 1.3 (Joint sum-one decomposition).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/ActualZhuSourceProjectors.projector_sum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/ActualZhuSourceProjectors.projector_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Taking products over all coordinates and summing over the finite dependent grid gives the source unit, including the empty coordinate product in rank zero.

**Theorem 1.4 (Joint current eigenvalues).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/ActualZhuSourceProjectors.projector_eigen`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/ActualZhuSourceProjectors.projector_eigen` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every H_i acts on a joint source projector by its corresponding grid weight.

**Theorem 1.5 (All-alpha elimination).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/ActualZhuSourceProjectors.projector_survives`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/ActualZhuSourceProjectors.projector_survives` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiply each native alpha annihilator by a joint projector. A nonzero projector forces one complex scalar factor to vanish, hence the integral weight lies between minus energy(alpha) and energy(alpha). The entire family of alpha inequalities is used; coordinate bounds alone are not substituted.

**Theorem 1.6 (Scalar action of the full current subalgebra).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/ActualZhuSourceProjectors.current_scalar`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/ActualZhuSourceProjectors.current_scalar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Adjoin induction on actual current generators, scalars, sums and products shows that every current-algebra element acts by a scalar on each joint projector. The ambient Zhu algebra is never assumed commutative.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/ActualZhuSourceProjectors.coordinate_eigen`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/ActualZhuSourceProjectors.coordinate_sum`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/ActualZhuSourceProjectors.current_scalar`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/ActualZhuSourceProjectors.projector_eigen`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/ActualZhuSourceProjectors.projector_sum`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/ActualZhuSourceProjectors.projector_survives`
- Dependency: [D5/S3/VertexAlgebra/Lattice/ActualZhuMinimum](ActualZhuMinimum.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/ActualZhuSourceSupport](ActualZhuSourceSupport.md)
