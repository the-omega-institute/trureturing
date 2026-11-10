# Actual full unital complex Zhu algebra

## Abstract

Actual full unital complex Zhu algebra

**Definition 1.1 (The original full additive quotient).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/ActualZhuAlgebra.Q`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/ActualZhuAlgebra.Q` (`✓ std3`).

*Citation.* Fedor K. Popov (2026). *Lean_VOA, full Zhu quotient algebra and original-carrier residue laws*. URL: <https://github.com/Fedor-Popov/Lean_VOA/blob/013a799ca834a8a6b3afa8129e3e522025b3f45c/VOA/Modularity/ZhuAlgebraFinite.lean>.

*Commentary.*

Q(D) is exactly Carrier(D) modulo ActualZhuFinite.zhuO(D). It retains the existing quotient AddCommGroup and complex Module; no norm-four restriction, vacuum-descendant restriction, representation kernel or changed O is used.

**Definition 1.2 (Actual product on the original quotient).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/ActualZhuAlgebra.quotientProduct`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/ActualZhuAlgebra.quotientProduct` (`✓ std3`).

*Citation.* Fedor K. Popov (2026). *Lean_VOA, full Zhu quotient algebra and original-carrier residue laws*. URL: <https://github.com/Fedor-Popov/Lean_VOA/blob/013a799ca834a8a6b3afa8129e3e522025b3f45c/VOA/Modularity/ZhuAlgebraFinite.lean>.

*Commentary.*

The complex bilinear native star, composed with the quotient map, descends by Mathlib LinearMap.liftQ₂. Its two kernel inclusions are discharged by ActualZhuLeftIdeal.star_left_mem_zhuO and ActualZhuRightIdeal.star_right_mem_zhuO under positive definiteness.

**Theorem 1.3 (Representative multiplication).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/ActualZhuAlgebra.quotientProduct_mk`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/ActualZhuAlgebra.quotientProduct_mk` (`✓ std3`). ∎

*Citation.* Fedor K. Popov (2026). *Lean_VOA, full Zhu quotient algebra and original-carrier residue laws*. URL: <https://github.com/Fedor-Popov/Lean_VOA/blob/013a799ca834a8a6b3afa8129e3e522025b3f45c/VOA/Modularity/ZhuAlgebraFinite.lean>.

*Commentary.*

The descended product of the classes of u and v is the class of their original actual star. This representative multiplication identity reduces the quotient associativity and vacuum unit laws to the corresponding identities on original states.

**Definition 1.4 (Associative unital ring with the original additive group).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/ActualZhuAlgebra.quotientRing`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/ActualZhuAlgebra.quotientRing` (`✓ std3`).

*Citation.* Fedor K. Popov (2026). *Lean_VOA, full Zhu quotient algebra and original-carrier residue laws*. URL: <https://github.com/Fedor-Popov/Lean_VOA/blob/013a799ca834a8a6b3afa8129e3e522025b3f45c/VOA/Modularity/ZhuAlgebraFinite.lean>.

*Commentary.*

The multiplication is quotientProduct and one is the class of the original vacuum. The full actual associator proves associativity. The vacuum field gives the left unit; creation, creativity and the finite original energy decomposition give the right unit on every original state. The ring extends the existing quotient AddCommGroup directly. No stability or associativity hypothesis bundle is assumed.

**Definition 1.5 (Complex algebra with the original scalar action).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/ActualZhuAlgebra.quotientAlgebra`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/ActualZhuAlgebra.quotientAlgebra` (`✓ std3`).

*Citation.* Fedor K. Popov (2026). *Lean_VOA, full Zhu quotient algebra and original-carrier residue laws*. URL: <https://github.com/Fedor-Popov/Lean_VOA/blob/013a799ca834a8a6b3afa8129e3e522025b3f45c/VOA/Modularity/ZhuAlgebraFinite.lean>.

*Commentary.*

Algebra.ofModule uses bilinearity of quotientProduct and the existing quotient complex Module. Scalars act by their multiples of the vacuum class, with the same additive and scalar operations as the original quotient. This construction is a possibly noncommutative algebra; commutativity is not asserted.

**Theorem 1.6 (The vacuum survives the literal O).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/ActualZhuAlgebra.vacuum_not_mem_zhuO`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/ActualZhuAlgebra.vacuum_not_mem_zhuO` (`✓ std3`). ∎

*Citation.* Fedor K. Popov (2026). *Lean_VOA, full Zhu quotient algebra and original-carrier residue laws*. URL: <https://github.com/Fedor-Popov/Lean_VOA/blob/013a799ca834a8a6b3afa8129e3e522025b3f45c/VOA/Modularity/ZhuAlgebraFinite.lean>.

*Commentary.*

For positive-definite D, gradeProjection(D,0) kills every circle summand: decompose the unrestricted second state into its finite nonnegative energy components q, and use the actual mode grading to put the i-th term in energy K+q-i+1, which is strictly positive for i at most K. Linearity kills the full literal span O. The same projection fixes the nonzero original vacuum, so the vacuum does not belong to O. No claim that O is graded is made.

**Definition 1.7 (Nontriviality of the actual quotient algebra).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/ActualZhuAlgebra.quotientNontrivial`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/ActualZhuAlgebra.quotientNontrivial` (`✓ std3`).

*Citation.* Fedor K. Popov (2026). *Lean_VOA, full Zhu quotient algebra and original-carrier residue laws*. URL: <https://github.com/Fedor-Popov/Lean_VOA/blob/013a799ca834a8a6b3afa8129e3e522025b3f45c/VOA/Modularity/ZhuAlgebraFinite.lean>.

*Commentary.*

The vacuum class and zero are distinct by vacuum_not_mem_zhuO. Together with quotientRing, quotientAlgebra and the existing ActualZhuFinite.positive_definite_zhu_quotient_finite, this supplies a nonzero finite-dimensional associative unital complex algebra on exactly the original full quotient. Finite-dimensionality is reused, not reproved or renamed as new mathematical content.

The quotient ring and algebra construction adapts ZhuRing.lean from Fedor K. Popov, Lean_VOA commit 013a799ca834a8a6b3afa8129e3e522025b3f45c, Apache-2.0. Native Lean 4.35 and its pinned Mathlib differ from upstream Lean 4.30 and its Mathlib pin, as recorded in the reference note. Native Mathlib supplies generic bilinear quotient descent, and all original lattice field, grading, star, literal circle span, two ideal stabilities and associator proofs are reused. This is a literature-attested native port. The grade-zero separation argument retains the exact literal O, not a representation kernel.

The dependent-family audit remains incomplete: exact source reconstruction, an enrolled readout, the actual-positive law, whole-family variation and sensitivity, actual observational dependence and current source binding are still required. See https://github.com/the-omega-institute/trureturing/issues/28745.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/ActualZhuAlgebra.Q`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/ActualZhuAlgebra.quotientAlgebra`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/ActualZhuAlgebra.quotientNontrivial`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/ActualZhuAlgebra.quotientProduct`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/ActualZhuAlgebra.quotientProduct_mk`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/ActualZhuAlgebra.quotientRing`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/ActualZhuAlgebra.vacuum_not_mem_zhuO`
- Dependency: [D5/S3/VertexAlgebra/Lattice/ActualZhuLeftIdeal](ActualZhuLeftIdeal.md)
