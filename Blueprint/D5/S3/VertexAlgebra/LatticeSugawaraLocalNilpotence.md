# Unrestricted Actual Sugawara Local Nilpotence

## Abstract

The actual Sugawara one-mode lowers native oscillator degree and is locally nilpotent on every finite-support state.

D is the original integral symmetric even-diagonal lattice data, including rank zero and degenerate Gram matrices. H is any complex matrix, without an inverse, positivity or signature assumption. Carrier(D) is the original finite charge sum of multivariate polynomials. The nonnegative oscillator degree of a monomial d is sum_x (x.2+1)*d(x); charge energy is not included in this bound.

The original weighted Euler derivation and its actual Sugawara commutator are used directly. The supplier oscillatorEuler_monomial supplies the actual basis eigenvalue, and eulerMode_single gives its action in the original charge carrier. Coefficient separation compares the nonnegative output oscillator degree with the signed difference N-j, never truncated natural subtraction. No lower bound on total L0 energy or finite arbitrary-signature energy fiber is asserted.

**Definition 1.1 (Finite native oscillator bound).**

Lean statement: `D5/S3/VertexAlgebra/LatticeSugawaraLocalNilpotence.oscillatorBound`

*Formalization.* `D5/S3/VertexAlgebra/LatticeSugawaraLocalNilpotence.oscillatorBound` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

N(v) is the finite supremum of oscillatorEnergy(d) over the nonzero original charge/monomial coefficients of v. It is zero for the zero state and every degree-zero charged ground state.

**Theorem 1.2 (Signed degree of every actual power).**

Lean statement: `D5/S3/VertexAlgebra/LatticeSugawaraLocalNilpotence.one_pow_basis_euler`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeSugawaraLocalNilpotence.one_pow_basis_euler` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural j and every actual basis label a=(beta,d), E(L1^j a)=(oscillatorEnergy(d)-j)L1^j a, with the difference formed in Complex. The charge contribution is absent from E.

**Theorem 1.3 (Coefficient separation annihilates excessive powers).**

Lean statement: `D5/S3/VertexAlgebra/LatticeSugawaraLocalNilpotence.one_pow_basis_eq_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeSugawaraLocalNilpotence.one_pow_basis_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If j>oscillatorEnergy(d), every actual coefficient of L1^j a vanishes: its nonnegative output degree cannot equal the negative integer oscillatorEnergy(d)-j. This applies to all charges and arbitrary H.

**Theorem 1.4 (Every finite-support state is locally nilpotent).**

Lean statement: `D5/S3/VertexAlgebra/LatticeSugawaraLocalNilpotence.one_pow_eq_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeSugawaraLocalNilpotence.one_pow_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every actual state v and every natural j>N(v), the actual operator (sugawaraMode(D,H,1))^j sends v to zero. The native finite monomial expansion extends the basis argument to mixed degrees and mixed charges.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeSugawaraLocalNilpotence.one_pow_basis_eq_zero`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeSugawaraLocalNilpotence.one_pow_basis_euler`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeSugawaraLocalNilpotence.one_pow_eq_zero`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeSugawaraLocalNilpotence.oscillatorBound`
- Dependency: [D5/S3/VertexAlgebra/LatticeActualLZeroGrading](LatticeActualLZeroGrading.md)
