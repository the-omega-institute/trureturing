# The original EJA definite domain

## Abstract

For general finite real Euclidean Jordan algebras, positivity and unitality give the square-defect inequality and a Jordan definite domain, hence propagation from Jordan-generating idempotents.

**Definition 1.1 (Generation by products and linear combinations).**

Lean statement: `D5/S3/Topology/EJADefiniteDomain.JordanGenerates`

*Formalization.* `D5/S3/Topology/EJADefiniteDomain.JordanGenerates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A subset generates when every real submodule containing that subset and the unit and closed under the specified Jordan product is the full space. This permits generating frame families whose union fails to linearly span.

**Definition 1.2 (The full mixed domain).**

Lean statement: `D5/S3/Topology/EJADefiniteDomain.mixedDomain`

*Formalization.* `D5/S3/Topology/EJADefiniteDomain.mixedDomain` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real submodule consists of a such that Phi(a∘x)=Phi(a)∘Phi(x) for every original real x. For a positive unital map, the zero-square-defect theorem identifies this with the original set Delta(a)=0.

**Theorem 1.3 (The original positive-map inequality).**

Lean statement: `D5/S3/Topology/EJADefiniteDomain.square_defect`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/EJADefiniteDomain.square_defect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual spectral resolution of A supplies the original finite spectral supplier. The derived target JB realization is passed to JBSquareDefect.square_defect_of_spectral for the same Phi. The original square_defect_identity exposes equation 75.12: with b=Phi(a), z_i=Phi(e_i), the sum of P_(r_i v-b)(z_i) equals Phi(a²)-b². Its three sums are Phi(a²), -2b² and b². Every summand is an actual square by unrestricted quadratic positivity, and their sum is an actual square. No square-defect or spectral condition is assumed as model data.

**Theorem 1.4 (The complete mixed identity).**

Lean statement: `D5/S3/Topology/EJADefiniteDomain.mixed_of_zero_defect`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/EJADefiniteDomain.mixed_of_zero_defect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original zero_defect_cross proof is reused at the derived target JB realization. A vanishing defect at a forces Phi(a∘x)=Phi(a)∘Phi(x) for every real x, by the two signed affine perturbations and their uniform norm bound. The original private proof is made public at its owner; no second proof is introduced.

**Theorem 1.5 (The zero-defect domain is Jordan closed).**

Lean statement: `D5/S3/Topology/EJADefiniteDomain.domain_jordan_closed`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/EJADefiniteDomain.domain_jordan_closed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The domain contains the original unit and is a real submodule. If a lies in it, the ordinary Jordan identity at a,a writes a²∘a² as a∘(a∘a²). Applying the full mixed identity twice and Delta(a)=0 gives Delta(a²)=0. The zero-defect theorem puts a² in the same mixed domain. Polarizing (a+b)²-a²-b² then proves closure under a∘b. Thus linear closure alone is not substituted for Jordan closure.

**Theorem 1.6 (Propagation from a genuine Jordan-generating family).**

Lean statement: `D5/S3/Topology/EJADefiniteDomain.multiplicative_of_jordan_generating`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/EJADefiniteDomain.multiplicative_of_jordan_generating` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose the same positive unital real linear map preserves the idempotence of every member of a Jordan-generating subset. These members have zero square defect and hence belong to the mixed domain. The unit and product closure force this domain to be all of X. All real products are therefore preserved. No linear-spanning, matrix, simplicity, injectivity or nonzero-image condition is required.

The source application is exactly Quantum Origin V 75.4(I), equations 75.12 and 75.13 and the definite-domain closure used for Jordan-generating frame families. Only the original bilinear product, unit, commutativity, Jordan identity and positive definite associative inner product are supplied. The proof includes Albert algebras, direct sums, rank one, zero images, repeated coefficients, zero idempotents and the zero algebra. It imposes no JB norm on the original Hilbert carrier.

This is a mathematical predecessor to the newest same-original-data Quantum Origin consumers. The weight-commutant closure, support normalization, faithful PRE reconstruction, full H13/C13 and remaining source clauses are separate obligations. There is no claim that the whole source atom or the later original physical reconstruction has been completed.

## References

- Truth anchor: `D5/S3/Topology/EJADefiniteDomain.JordanGenerates`
- Truth anchor: `D5/S3/Topology/EJADefiniteDomain.domain_jordan_closed`
- Truth anchor: `D5/S3/Topology/EJADefiniteDomain.mixedDomain`
- Truth anchor: `D5/S3/Topology/EJADefiniteDomain.mixed_of_zero_defect`
- Truth anchor: `D5/S3/Topology/EJADefiniteDomain.multiplicative_of_jordan_generating`
- Truth anchor: `D5/S3/Topology/EJADefiniteDomain.square_defect`
- Dependency: [D5/S3/Topology/EJASpectralNorm](EJASpectralNorm.md)
- Dependency: [D5/S3/Topology/JBSquareDefect](JBSquareDefect.md)
