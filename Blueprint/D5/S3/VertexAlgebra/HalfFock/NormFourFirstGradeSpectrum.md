# Twisted Norm-Four First-Grade Spectrum

## Abstract

Complete twisted norm-four first-grade spectrum and the literal parity-minus energy-two field.

Let D be finite-rank even integral symmetric lattice data with unit Gram determinant, let B be its bilinear form, and let a satisfy B(a,a)=4. Write r=rank(D), N=2^(r/2), U=groundAction(D,hu,a), and s for a complex source scalar. Evenness forces a to have nonzero reduction modulo two: a=2b would give B(b,b)=1. Thus its actual quotient charge is nonzero, the actual ground action has trace zero, and U squared is the identity. Positivity and rootlessness are unnecessary.

**Definition 1.1 (The complete native tensor and actual grade).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NormFourFirstGradeSpectrum.nativeGradeEquiv`

*Formalization.* `D5/S3/VertexAlgebra/HalfFock/NormFourFirstGradeSpectrum.nativeGradeEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every D and hu, the tensor product of the coordinate space C^r and the entire actual ground is linearly equivalent to actualGrade(D,hu,1). The complete production basis is reindexed by the fact that every odd-weight-one monomial is exactly X(i,0). The equivalence sends x tensor u to sum_i x_i X(i,0) tensor u; no identification premise or preferred subspace replaces the original grade.

**Definition 1.2 (Tensor formula).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NormFourFirstGradeSpectrum.nativeL`

*Formalization.* `D5/S3/VertexAlgebra/HalfFock/NormFourFirstGradeSpectrum.nativeL` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let R(x)=B(a,x)a/4 be the coordinate charge-line projection, Q+=(I+sU)/2 and Q-=(I-sU)/2. The native tensor endomorphism is (1/16)(I tensor Q+)+(1/2)(R tensor Q-). These formulas use the actual ground action.

**Theorem 1.3 (Conjugacy with the actual corrected field).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NormFourFirstGradeSpectrum.actualZeroMode_transport`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/NormFourFirstGradeSpectrum.actualZeroMode_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D, hu, norm-four a and arbitrary complex s, actualGradeOneZeroMode equals the conjugate of nativeL under nativeGradeEquiv. Applying both sides to every element of the complete production basis gives the actual corrected coefficient formula from NormFourLowestGrades.zeroMode_X. This establishes operator conjugacy on the whole grade, not only equality of cubics.

**Definition 1.4 (Zero-eigenvalue projection).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NormFourFirstGradeSpectrum.actualProjectorZero`

*Formalization.* `D5/S3/VertexAlgebra/HalfFock/NormFourFirstGradeSpectrum.actualProjectorZero` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Conjugate (I-R) tensor Q- to the entire actual first grade.

**Definition 1.5 (One-sixteenth-eigenvalue projection).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NormFourFirstGradeSpectrum.actualProjectorSixteen`

*Formalization.* `D5/S3/VertexAlgebra/HalfFock/NormFourFirstGradeSpectrum.actualProjectorSixteen` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Conjugate I tensor Q+ to the entire actual first grade.

**Definition 1.6 (One-half-eigenvalue projection).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NormFourFirstGradeSpectrum.actualProjectorHalf`

*Formalization.* `D5/S3/VertexAlgebra/HalfFock/NormFourFirstGradeSpectrum.actualProjectorHalf` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Conjugate R tensor Q- to the entire actual first grade.

**Theorem 1.7 (Complete spectral projections).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NormFourFirstGradeSpectrum.actual_projectors_complete`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/NormFourFirstGradeSpectrum.actual_projectors_complete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D, hu, norm-four a and s with s squared equal to one, the three actual projectors sum to the identity. Each is an IsProj onto the whole eigenspace of actualGradeOneZeroMode at respectively 0, 1/16 and 1/2, and each range equals that eigenspace. The tensor charge and ground projections give the eigenrelations in both orders. For any vector in one eigenspace, scalar cancellation kills the other two projections, so completeness makes its own projection the identity.

**Theorem 1.8 (Actual tensor-product traces).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NormFourFirstGradeSpectrum.actual_projectors_traces`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/NormFourFirstGradeSpectrum.actual_projectors_traces` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D, hu, norm-four a and arbitrary complex s, the traces on the complete actual first grade of the three displayed endomorphisms are (r-1)N/2, rN/2 and N/2. Conjugation preserves trace; tensor-product traces multiply; R has trace one, while both ground factors have trace N/2. The trace formula itself requires no sign-square premise.

**Theorem 1.9 (Integral multiplicity equations).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NormFourFirstGradeSpectrum.actual_first_grade_eigenspace_multiplicities`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/NormFourFirstGradeSpectrum.actual_first_grade_eigenspace_multiplicities` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D, hu, norm-four a and s with s squared equal to one, let d0, d16 and dh be the complex dimensions of the whole actual first-grade eigenspaces at 0, 1/16 and 1/2. Then 2d0=(r-1)N, 2d16=rN and 2dh=N. Each equality follows from the trace of the actual projection onto its full eigenspace. Positive rank follows from norm four and is used only to interpret the natural-number subtraction.

**Definition 1.10 (The actual fixed source).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NormFourFirstGradeSpectrum.normFourFixedSource`

*Formalization.* `D5/S3/VertexAlgebra/HalfFock/NormFourFirstGradeSpectrum.normFourFixedSource` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every D, a and arbitrary complex s, vector(D,a,s) is theta-fixed: reflection negates its charge polynomial, fixes its square, and exchanges the two charged ground states. The resulting FixedCarrier element is the literal source of fixedParitySlice. The source scalar s is independent of the target parity -1.

**Definition 1.11 (The ambient parity-minus energy-two intersection).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NormFourFirstGradeSpectrum.parityMinusEnergyTwo`

*Formalization.* `D5/S3/VertexAlgebra/HalfFock/NormFourFirstGradeSpectrum.parityMinusEnergyTwo` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This submodule is literally paritySpace(D,hu,-1) intersect eigenspace(actualTensorL0(D,hu),2), in the original entire ActualTensor carrier.

**Theorem 1.12 (Exact whole-space identification at rank twenty-four).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NormFourFirstGradeSpectrum.actual_grade_one_eq_parity_minus_energy_two`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/NormFourFirstGradeSpectrum.actual_grade_one_eq_parity_minus_energy_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every rank-twenty-four D with unit determinant, actualGrade(D,hu,1) equals the entire ambient parity-minus energy-two intersection. The original L0 grading identifies actualGrade1 with the whole energy-two eigenspace; actualParity_on_actualGrade makes every vector of this grade have parity -1. The reverse containment uses only the ambient energy equation. No norm-four charge, positivity or rootlessness premise is required.

**Definition 1.13 (The literal physical mode on the whole intersection).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NormFourFirstGradeSpectrum.parityMinusEnergyTwoZeroMode`

*Formalization.* `D5/S3/VertexAlgebra/HalfFock/NormFourFirstGradeSpectrum.parityMinusEnergyTwoZeroMode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At rank twenty-four and for norm-four a, restrict the original corrected coefficient -4 to parityMinusEnergyTwo. Invariance follows from the whole-grade equality and actualGradeOneZeroMode. The same endomorphism, under the typed inclusion into paritySpace(-1), is ncoeff1 of fixedParitySlice(D,hu,-1,normFourFixedSource(D,a,s)): ncoeff1 selects exponent -2, whose native doubled exponent is -4.

**Theorem 1.14 (Complete ambient physical spectrum).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NormFourFirstGradeSpectrum.actual_parity_minus_energy_two_multiplicities`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/NormFourFirstGradeSpectrum.actual_parity_minus_energy_two_multiplicities` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every rank-twenty-four D with unit Gram determinant, every norm-four a, and every complex source scalar s with s squared equal to one, parityMinusEnergyTwo has dimension 98304. The whole eigenspaces of its literal restricted fixedParitySlice physical mode have dimensions 47104 at 0, 49152 at 1/16 and 2048 at 1/2. The theorem also states the exact typed inclusion identity with fixedParitySlice.ncoeff1 for every vector of the full intersection. Eigenspaces are transported by the exact submodule equality, retaining all vectors.

This is classical twisted lattice linear algebra: Frenkel-Lepowsky-Meurman, Vertex Operator Algebras and the Monster; Dong-Nagatomo, arXiv:math/9808088, section 3.2; Bakalov-Kac, arXiv:math/0402315, section 4. The norm-four source formula follows Shimakura, arXiv:1202.6107, equation (1.3). Formalization of the actual fields and whole eigenspaces asserts no literature novelty. These results do not construct an orbifold vertex algebra, a twisted intertwiner extension, a Monster action or VOA, or fusion, string-theory or AdS/CFT structures.

## References

- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NormFourFirstGradeSpectrum.actualProjectorHalf`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NormFourFirstGradeSpectrum.actualProjectorSixteen`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NormFourFirstGradeSpectrum.actualProjectorZero`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NormFourFirstGradeSpectrum.actualZeroMode_transport`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NormFourFirstGradeSpectrum.actual_first_grade_eigenspace_multiplicities`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NormFourFirstGradeSpectrum.actual_grade_one_eq_parity_minus_energy_two`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NormFourFirstGradeSpectrum.actual_parity_minus_energy_two_multiplicities`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NormFourFirstGradeSpectrum.actual_projectors_complete`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NormFourFirstGradeSpectrum.actual_projectors_traces`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NormFourFirstGradeSpectrum.nativeGradeEquiv`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NormFourFirstGradeSpectrum.nativeL`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NormFourFirstGradeSpectrum.normFourFixedSource`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NormFourFirstGradeSpectrum.parityMinusEnergyTwo`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NormFourFirstGradeSpectrum.parityMinusEnergyTwoZeroMode`
- Dependency: [D5/S3/VertexAlgebra/HalfFock/LatticeHalfFockParityField](LatticeHalfFockParityField.md)
- Dependency: [D5/S3/VertexAlgebra/HalfFock/NormFourLowestGrades](NormFourLowestGrades.md)
