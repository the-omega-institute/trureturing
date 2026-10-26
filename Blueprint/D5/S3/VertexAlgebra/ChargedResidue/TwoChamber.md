# TwoChamber

## Abstract

Formal collision residue coefficients.

**Theorem 1.1 (The two signed chamber coefficients).**

Lean statement: `D5/S3/VertexAlgebra/ChargedResidue/TwoChamber.two_chamber_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/ChargedResidue/TwoChamber.two_chamber_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For all integer exponents a,b and coefficient index v, the signed difference between the coefficients at v and a+b-v of (1-X)^a*(1+X)^b equals the two local pole coefficients. Negative indices are extended by zero. Multiplication by 1-X and 1+X gives finite recurrences from a common negative exponent. The base case uses the quadratic coefficient change with its Jacobian, even and odd indices, and the interval where both input coefficients vanish.

**Theorem 1.2 (The complete signed scalar collision comparison).**

Lean statement: `D5/S3/VertexAlgebra/ChargedResidue/TwoChamber.signed_two_chamber_scalar`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/ChargedResidue/TwoChamber.signed_two_chamber_scalar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Specializing a=q+B and b=q-B identifies the two local coefficients with collisionScalar(v-2*q-2,B,-q-1-B) and its reflected B branch. Each branch keeps its own negative-degree test. The factors are 2^(-2*B)/2 and (-1)^v*2^(2*B)/2. The native outer-cutoff regrouping and reflected oscillator and ground-action identities connect this scalar formula to the arbitrary-input physical forward law. Each whole ordered range is enlarged before its monomial expansion.

## References

- Truth anchor: `D5/S3/VertexAlgebra/ChargedResidue/TwoChamber.signed_two_chamber_scalar`
- Truth anchor: `D5/S3/VertexAlgebra/ChargedResidue/TwoChamber.two_chamber_coefficient`
- Dependency: [D5/S3/VertexAlgebra/ChargedResidue/QuadraticResidue](QuadraticResidue.md)
