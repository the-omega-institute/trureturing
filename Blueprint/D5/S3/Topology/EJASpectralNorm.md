# The spectral norm of an original finite real EJA

## Abstract

The spectral JB norm is constructed from the original finite real Euclidean Jordan laws on a separate type copy.

**Definition 1.1 (Normalized inner functionals).**

Lean statement: `D5/S3/Topology/EJASpectralNorm.coeff`

*Formalization.* `D5/S3/Topology/EJASpectralNorm.coeff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an idempotent c the functional is x ↦ inner(c,x)/inner(c,c). A nonzero c gives a positive functional on every actual Jordan square and takes value one on the original unit. At c=0 division by zero gives the zero functional. Its inclusion only adjoins zero to the set of readouts.

**Definition 1.2 (All idempotent readouts).**

Lean statement: `D5/S3/Topology/EJASpectralNorm.values`

*Formalization.* `D5/S3/Topology/EJASpectralNorm.values` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The value set consists of the absolute normalized inner functional values at all original idempotents, with no chosen spectral family or primitive-frame premise.

**Definition 1.3 (The spectral norm).**

Lean statement: `D5/S3/Topology/EJASpectralNorm.spectralNorm`

*Formalization.* `D5/S3/Topology/EJASpectralNorm.spectralNorm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

N(x) is the supremum of the nonempty set of absolute idempotent readouts. For any actual complete spectral resolution the supremum is the maximum of zero and |r_i| over the nonzero e_i. Coefficients attached to zero idempotents never constrain the value. The empty family and the zero algebra are included.

**Definition 1.4 (A separate normed type copy).**

Lean statement: `D5/S3/Topology/EJASpectralNorm.Space`

*Formalization.* `D5/S3/Topology/EJASpectralNorm.Space` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Space(A) is an algebraic type copy of the original carrier. The given Hilbert norm and inner product on X are retained. Only this copy receives the newly derived spectral norm.

**Definition 1.5 (The original-carrier identification).**

Lean statement: `D5/S3/Topology/EJASpectralNorm.equiv`

*Formalization.* `D5/S3/Topology/EJASpectralNorm.equiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The identity of underlying elements is a real linear equivalence from the type copy back to X. It transports the product, unit and actual square-root witnesses exactly.

**Definition 1.6 (The original product on the copy).**

Lean statement: `D5/S3/Topology/EJASpectralNorm.product`

*Formalization.* `D5/S3/Topology/EJASpectralNorm.product` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The bilinear product on Space(A) is exactly the original real bilinear S, transported along equiv. No matrix or associative representation is introduced.

**Definition 1.7 (The original additive operations).**

Lean statement: `D5/S3/Topology/EJASpectralNorm.spaceAdd`

*Formalization.* `D5/S3/Topology/EJASpectralNorm.spaceAdd` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The additive commutative group is transported from X without changing its operations.

**Definition 1.8 (The original real scalar action).**

Lean statement: `D5/S3/Topology/EJASpectralNorm.spaceModule`

*Formalization.* `D5/S3/Topology/EJASpectralNorm.spaceModule` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real module structure uses exactly the original scalar multiplication.

**Definition 1.9 (The newly constructed norm).**

Lean statement: `D5/S3/Topology/EJASpectralNorm.spaceNorm`

*Formalization.* `D5/S3/Topology/EJASpectralNorm.spaceNorm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The norm of a copied element is the supremum spectralNorm of its original-carrier identification.

**Definition 1.10 (The normed additive group).**

Lean statement: `D5/S3/Topology/EJASpectralNorm.spaceNormedAddCommGroup`

*Formalization.* `D5/S3/Topology/EJASpectralNorm.spaceNormedAddCommGroup` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

NormedAddCommGroup.ofCore uses the proved spectral norm core to supply the distance and normed-group laws on the copy.

**Definition 1.11 (The normed real vector space).**

Lean statement: `D5/S3/Topology/EJASpectralNorm.spaceNormedSpace`

*Formalization.* `D5/S3/Topology/EJASpectralNorm.spaceNormedSpace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

NormedSpace.ofCore uses the same core and original scalar action. This is the normed space passed to the general six-law JB results.

**Definition 1.12 (Finite dimensionality of the copy).**

Lean statement: `D5/S3/Topology/EJASpectralNorm.spaceFinite`

*Formalization.* `D5/S3/Topology/EJASpectralNorm.spaceFinite` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real linear equivalence to the original X transfers finite dimensionality by the existing Mathlib theorem.

**Definition 1.13 (Completeness of the copy).**

Lean statement: `D5/S3/Topology/EJASpectralNorm.spaceComplete`

*Formalization.* `D5/S3/Topology/EJASpectralNorm.spaceComplete` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

FiniteDimensional.complete supplies completeness for the constructed normed real space, including dimension zero.

**Theorem 1.14 (The spectral norm core).**

Lean statement: `D5/S3/Topology/EJASpectralNorm.norm_core`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/EJASpectralNorm.norm_core` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The nonnegative supremum, scalar homogeneity, triangle inequality and definiteness supply a NormedSpace.Core on the algebraic copy. Both the normed additive group and the normed real space are constructed from this same core.

**Theorem 1.15 (The derived JB realization).**

Lean statement: `D5/S3/Topology/EJASpectralNorm.jb_data`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/EJASpectralNorm.jb_data` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The three algebraic laws are transported from the original EJA data. Positivity of idempotent inner functionals follows from the licensed single-idempotent Peirce projections. A complete actual spectrum bounds every functional by the largest nonzero-idempotent coefficient, while the same idempotents read each such coefficient back. These bounds prove finiteness and definiteness, including zero units and zero idempotents. Functional linearity proves the triangle and homogeneity laws. Square reconstruction proves N(x²)=N(x)². Positivity gives N(x²)≤N(x²+y²). For the same actual pair x,y, positivity of each functional on (t x+y)² and the quadratic discriminant give the Cauchy inequality; the square norm law then gives N(x∘y)≤N(x)N(y). Finite dimensionality gives completeness of the normed copy. Thus the full six JB laws are derived, with no norm law, cone selfduality, trace normalization, simplicity, representation, specialness or primitive-frame hypothesis.

The private Peirce and inner-product dependency is adapted from Bryan Ehrlich, ehrlich-b/euclidean-jordan at immutable revision a83407e4dbf73c77c31a2291c02f20b37a5ebbaf, EuclideanJordan/Bridge.lean, EuclideanJordan/Peirce.lean and EuclideanJordan/Order.lean. The Apache-2.0 license and authorship are retained at docs/reports/third-party/euclidean-jordan-LICENSE.txt. The two needed original results are inner_mul_self_nonneg_of_idem and inner_left_coeff. Their hypotheses are precisely bilinearity, commutativity, the ordinary Jordan identity and inner associativity; no order, trace or special representation occurs.

The application to Quantum Origin V 75.4(I) is the missing norm bridge needed to invoke the existing general JB quadratic-positivity and square-defect results on the original finite EJA carrier. This construction does not supply weight commutants, support normalization, the two PRE interfaces or the full H13/C13 consumers. Albert algebras, nonisomorphic direct sums, rank one and the zero algebra remain within the original data interface.

## References

- Truth anchor: `D5/S3/Topology/EJASpectralNorm.Space`
- Truth anchor: `D5/S3/Topology/EJASpectralNorm.coeff`
- Truth anchor: `D5/S3/Topology/EJASpectralNorm.equiv`
- Truth anchor: `D5/S3/Topology/EJASpectralNorm.jb_data`
- Truth anchor: `D5/S3/Topology/EJASpectralNorm.norm_core`
- Truth anchor: `D5/S3/Topology/EJASpectralNorm.product`
- Truth anchor: `D5/S3/Topology/EJASpectralNorm.spaceAdd`
- Truth anchor: `D5/S3/Topology/EJASpectralNorm.spaceComplete`
- Truth anchor: `D5/S3/Topology/EJASpectralNorm.spaceFinite`
- Truth anchor: `D5/S3/Topology/EJASpectralNorm.spaceModule`
- Truth anchor: `D5/S3/Topology/EJASpectralNorm.spaceNorm`
- Truth anchor: `D5/S3/Topology/EJASpectralNorm.spaceNormedAddCommGroup`
- Truth anchor: `D5/S3/Topology/EJASpectralNorm.spaceNormedSpace`
- Truth anchor: `D5/S3/Topology/EJASpectralNorm.spectralNorm`
- Truth anchor: `D5/S3/Topology/EJASpectralNorm.values`
- Dependency: [D5/S3/Topology/EJAFiniteSpectral](EJAFiniteSpectral.md)
- Dependency: [D5/S3/Topology/JBAlgebra](JBAlgebra.md)
