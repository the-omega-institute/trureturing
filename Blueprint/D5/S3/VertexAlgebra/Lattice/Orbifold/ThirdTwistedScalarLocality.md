# Order-Three Scalar Contraction Clearing

## Abstract

The order-three contraction clears to one finite homogeneous numerator in rational and formal expansions.

For the cover coordinates x = z^(1/3) and y = w^(1/3), use the ratio t = y/x in the binomial product of Bakalov–Kac, arXiv:math/0402315v3, §4, Lemma 4.2, equation (4.34). Let D be the lattice, g an additive equivalence of its charges, and u a primitive cubic root when factoring x³ − y³. The three orbit pairings may have either sign.

**Definition 1.1 (Integral orbit pairing).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedScalarLocality.contractionOrbitExponent`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedScalarLocality.contractionOrbitExponent` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

The exponent eⱼ for charges a and b is the integral pairing ⟨gʲa,b⟩.

**Definition 1.2 (Clearing order).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedScalarLocality.contractionLocalityOrder`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedScalarLocality.contractionLocalityOrder` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Take the maximum of the three negative parts max(0, −eⱼ) for j = 0, 1, 2.

**Theorem 1.3 (Nonnegative cleared exponents).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedScalarLocality.contractionLocalityOrder_add_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedScalarLocality.contractionLocalityOrder_add_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

At the clearing order N, each N + eⱼ with j = 0, 1, 2 is nonnegative.

**Definition 1.4 (Two-variable numerator).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedScalarLocality.clearedContractionNumerator`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedScalarLocality.clearedContractionNumerator` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For any complex unit u and natural order N, form the product of the three linear polynomials x − uʲy to the natural powers max(0, N + eⱼ). When every N + eⱼ is nonnegative, the exponents are exactly N + eⱼ and the product is homogeneous of degree 3N + ∑ⱼ eⱼ.

**Theorem 1.5 (Evaluation of the numerator).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedScalarLocality.clearedContractionNumerator_eval`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedScalarLocality.clearedContractionNumerator_eval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For a coefficient map C from ℂ into a commutative ring, evaluation at x and y gives the product of x − C(uʲ)y to the natural powers max(0, N + eⱼ).

**Theorem 1.6 (Homogeneous rational clearing).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedScalarLocality.rationalContraction_clear_homogeneous`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedScalarLocality.rationalContraction_clear_homogeneous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For rational functions x and y with x ≠ 0 and x³ − y³ ≠ 0, the rational contraction at y/x is multiplied by the orbit monomial x^(∑ⱼ eⱼ) and by (x³ − y³)^N. The result is the evaluation of the two-variable numerator whenever u is primitive of order three and every N + eⱼ is nonnegative.

**Definition 1.7 (Numerator in the ratio coordinate).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedScalarLocality.clearedContractionTaylorPolynomial`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedScalarLocality.clearedContractionTaylorPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Evaluate the two-variable numerator at x = 1 and y = X to obtain a polynomial in the ratio coordinate.

**Theorem 1.8 (Homogeneous clearing after formal expansion).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedScalarLocality.binomialContraction_clear_homogeneous`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedScalarLocality.binomialContraction_clear_homogeneous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Let F map complex formal power series into a commutative ring, let x be a unit there, and put y = x F(X). For a primitive cubic root u and an order N with every N + eⱼ nonnegative, multiply the image under F of the binomial units to their integer powers eⱼ by the unit monomial x^(∑ⱼ eⱼ) and by (x³ − y³)^N. This gives the same polynomial evaluated at x and y with coefficient map F ∘ C, where C includes the complex constants as power series.

**Theorem 1.9 (Clearing the scalar contraction at X).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedScalarLocality.scalar_contraction_X_clear`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedScalarLocality.scalar_contraction_X_clear` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

At the Bakalov–Kac root ζ, multiply the scalar contraction exponential by (1 − X³)^N. The result is the ratio-coordinate polynomial viewed as a power series whenever every N + eⱼ is nonnegative. The rational product and the scalar exponential agree through the Laurent expansion at X.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedScalarLocality.binomialContraction_clear_homogeneous`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedScalarLocality.clearedContractionNumerator`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedScalarLocality.clearedContractionNumerator_eval`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedScalarLocality.clearedContractionTaylorPolynomial`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedScalarLocality.contractionLocalityOrder`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedScalarLocality.contractionLocalityOrder_add_nonneg`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedScalarLocality.contractionOrbitExponent`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedScalarLocality.rationalContraction_clear_homogeneous`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedScalarLocality.scalar_contraction_X_clear`
- Dependency: [D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedContractionReciprocity](ThirdTwistedContractionReciprocity.md)
