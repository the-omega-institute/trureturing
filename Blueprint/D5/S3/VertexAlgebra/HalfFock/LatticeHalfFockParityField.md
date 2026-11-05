# Target parity transport and fixed-source fields

## Abstract

Actual target-parity transport for corrected half-Fock fields.

Let D be any finite-rank integral symmetric even lattice datum and hu:IsUnit D.G.det. The source Carrier D and target ActualTensor D hu remain distinct. The target operator is the existing oscillator sigma tensored with the identity on the actual quotient ground module. No positivity, Jacobi, equivariance premise, conformal covariance or desired transport law is assumed.

**Theorem 1.1 (Corrected fields intertwine source theta with actual target parity).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/LatticeHalfFockParityField.correctedField_target_parity`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/LatticeHalfFockParityField.correctedField_target_parity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For every source a, signed exponent e and actual target x, actualParity applied to the coefficient of correctedField a equals the coefficient of correctedField (theta a) applied to actualParity x. The proof starts with the charged oscillator kernel, propagates through the signed jet recursion and both flatCoefficient branches, then through the pointwise finite normal-word, correction and charge sums. Coordinate monodromy is not substituted for this target action.

**Definition 1.2 (Fixed-source fields restrict to the actual parity sectors).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/LatticeHalfFockParityField.fixedParitySlice`

*Formalization.* `D5/S3/VertexAlgebra/HalfFock/LatticeHalfFockParityField.fixedParitySlice` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For any s:Complex and fixed source a, paritySpace D hu s is the kernel of actualParity-s identity. The target/source identity proves that correctedField a preserves this subspace. fixedParitySlice uses the actual lower-truncated Hahn field and its original support bound, with coefficient 2*e for the integral-power restriction. Taking s=1 and s=-1 gives the two target parity sectors. This is a consumed sector action; it does not assert twisted Jacobi, an orbifold extension, fusion, Monster symmetry, string theory or AdS/CFT.

Classical provenance: Dong--Nagatomo, math/9808088v1, section 3.2, and Bakalov--Kac, math/0402315v1. The kernel calculation and its propagation are repository-derived implementations of the existing lattice construction; no literature novelty is claimed.

## References

- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/LatticeHalfFockParityField.correctedField_target_parity`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/LatticeHalfFockParityField.fixedParitySlice`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockCorrectedMonodromy](../LatticeHalfFockCorrectedMonodromy.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockParityT](../LatticeHalfFockParityT.md)
