# Adjoints of the Odd Norm-Four Axis Modes

## Abstract

Hermitian adjoints for norm-four axis modes on the actual odd twisted sector.

Let D be lattice data with unit Gram determinant, and let H be the inherited tensor form on the actual negative parity sector. For a charge a and a complex parameter s, write L(s,n) for coefficient n + 1 of the negative parity slice of the actual fixed source `D5/S3/VertexAlgebra/HalfFock/NormFourFirstGradeSpectrum.normFourFixedSource`.

**Theorem 1.1 (Adjoint with conjugated source parameter).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NormFourAxisAdjoint.mode_adjoint`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/NormFourAxisAdjoint.mode_adjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If B(a,a) = 4, then H(L(s,n)x,y) = H(x,L(t,−n)y), where t is the complex conjugate of s. This holds for every complex s, integer n, and pair of odd twisted states x and y.

**Theorem 1.2 (Positive form and opposite-mode adjoints).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NormFourAxisAdjoint.ising_mode_adjoint`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/NormFourAxisAdjoint.ising_mode_adjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the real Gram matrix is positive definite, B(a,a) = 4, and s² = 1. The real part of H(x,x) is positive for every nonzero odd twisted x, and H(L(s,n)x,y) = H(x,L(s,−n)y) for all integer n and odd twisted x and y.

## References

- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NormFourAxisAdjoint.ising_mode_adjoint`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NormFourAxisAdjoint.mode_adjoint`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NormFourFirstGradeSpectrum.normFourFixedSource`
- Dependency: [D5/S3/VertexAlgebra/HalfFock/Hermitian/LatticeHalfFockChargedHermitian](Hermitian/LatticeHalfFockChargedHermitian.md)
- Dependency: [D5/S3/VertexAlgebra/HalfFock/Hermitian/LatticeHalfFockSugawaraHermitian](Hermitian/LatticeHalfFockSugawaraHermitian.md)
- Dependency: [D5/S3/VertexAlgebra/HalfFock/NormFourFirstGradeSpectrum](NormFourFirstGradeSpectrum.md)
