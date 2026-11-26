# Order-Three Twisted Lattice Contraction

## Abstract

The normalized scalar contraction and its complementary Fourier coefficient for a cubic lattice twist.

Let D be the native even integral lattice and g an additive equivalence of its charges. Write ⟨a,b⟩ for the lattice pairing and extend it complex bilinearly using D's Gram matrix.

**Theorem 1.1 (The normalized scalar product).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedContraction.scalar_contraction`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedContraction.scalar_contraction` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

In Lemma 4.2, equation (4.34) of arXiv:math/0402315v3, factor out the powers of z and put X = (w/z)^(1/3). The normalized factor is the product of (1 − ζʲX) raised to ⟨gʲa,b⟩ for j = 0, 1, 2. These are integer powers of units in the power-series ring. The product equals the formal exponential of the series with constant term zero and degree-n coefficient −Σⱼ ⟨gʲa,b⟩ζ^(jn)/n for n > 0. The Lean identity holds for any complex ζ.

**Theorem 1.2 (Pairing the complementary Fourier components).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedContraction.coeff_contractionExponent_opposite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedContraction.coeff_contractionExponent_opposite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Assume g³ = 1, g preserves the pairing, and ζ³ = 1. For n > 0 put u = ζ^(n mod 3) and Pᵤ(a) = (a + u g a + u² g² a)/3 in the complexified lattice. The degree-n coefficient of the exponent is −⟨Pᵤ(a), P_(u²)(b)⟩/(n/3). The two components have eigenvalues u⁻¹ and u under the complex extension of g.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedContraction.coeff_contractionExponent_opposite`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedContraction.scalar_contraction`
- Dependency: [D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeCocycle](ThirdTwistedChargeCocycle.md)
