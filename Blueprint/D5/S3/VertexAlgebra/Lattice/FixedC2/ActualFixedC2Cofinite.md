# C2 Cofiniteness of the Sign-Fixed Leech Lattice Vertex Algebra

## Abstract

The actual sign-fixed Leech lattice vertex algebra has a finite-dimensional intrinsic C2 quotient.

**Theorem 1.1 (The intrinsic fixed quotient is finite-dimensional over the complex numbers).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2Cofinite.leech_fixed_c2_cofinite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2Cofinite.leech_fixed_c2_cofinite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The quotient is the sign-fixed carrier of the actual Leech lattice vertex algebra modulo the complex span of actual (-2)-products of pairs of fixed states.

Charge descent shows that the quotient is spanned by the orbit images for the finitely many charges in the closed Gram-coordinate box. The orbit of zero is exactly the fixed vacuum-charge space, since support at zero is equivalent to being the insertion of a single oscillator polynomial there. The bounded even words give a finite spanning family for its image. For every nonzero orbit the image is contained in the span of neutral multiples of the ground and first oscillator classes, which is also finite-dimensional. The finite sum of these subspaces is the whole quotient.

Abe, arXiv:math/0311210, Theorem 7.1(2), records fixed lattice C2 cofiniteness and cites Yamskulna. The formal proof here uses the actual Leech state-field modes and the explicit short charge and oscillator reductions.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2Cofinite.leech_fixed_c2_cofinite`
- Dependency: [D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2ChargedOrbit](ActualFixedC2ChargedOrbit.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2ChargedOrbitFinite](ActualFixedC2ChargedOrbitFinite.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2NeutralFinite](ActualFixedC2NeutralFinite.md)
