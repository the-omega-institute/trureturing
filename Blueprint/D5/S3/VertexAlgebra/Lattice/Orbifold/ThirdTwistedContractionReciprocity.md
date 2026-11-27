# Order-Three Rational Contraction Reciprocity

## Abstract

Rational contraction reciprocity and cancellation by the order-three charge multiplier.

Let D be the native even integral lattice with pairing ⟨a,b⟩ and let g be an additive equivalence of its charges. The rational contraction uses the cover ratio t = (w/z)^(1/3) from Bakalov–Kac, arXiv:math/0402315v3, Lemma 4.2, equation (4.34). Write N = 1 + g + g² for the integral orbit norm.

**Definition 1.1 (Rational contraction).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedContractionReciprocity.rationalContraction`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedContractionReciprocity.rationalContraction` (`✓ std3`).

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For a complex unit u, multiply the three binomials 1 − uʲt to their integer powers ⟨gʲa,b⟩ in the complex rational-function field.

**Definition 1.2 (Reciprocity phase).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedContractionReciprocity.reciprocityPhase`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedContractionReciprocity.reciprocityPhase` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

The phase is the product of the complex units −uʲ raised to the respective integer powers ⟨gʲa,b⟩.

**Theorem 1.3 (Reciprocity under charge and ratio reversal).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedContractionReciprocity.rationalContraction_reciprocity`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedContractionReciprocity.rationalContraction_reciprocity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Assume g is a pairing isometry, g³ = 1, u³ = 1, and t is nonzero. Inverting each binomial gives a factor of t times its leading coefficient. The factors of t combine with exponent ⟨Na,b⟩. Symmetry and isometry identify the product with inverted root parameter with the product on the reversed charges.

**Theorem 1.4 (Laurent expansion at the indeterminate).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedContractionReciprocity.rationalContraction_X_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedContractionReciprocity.rationalContraction_X_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

At the indeterminate X, the Laurent expansion is the product of the power-series binomial units with the same integer powers. This is the product appearing in `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedContraction.scalar_contraction` with complex parameter u. The expansion holds for every complex unit u.

**Theorem 1.5 (Cancellation by the charge multiplier).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedContractionReciprocity.c_mul_reciprocityPhase`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedContractionReciprocity.c_mul_reciprocityPhase` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For ζ = exp(2πi/3), the phase multiplies the Bakalov–Kac coefficient `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeCocycle.c` on (a,b) to give its value on (b,a). The two nontrivial cyclotomic factors of B exchange, and the binomial sign at j = 0 cancels the sign from ε.

**Theorem 1.6 (Reciprocity of the cocycle-weighted contraction).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedContractionReciprocity.c_mul_rationalContraction_reciprocity`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedContractionReciprocity.c_mul_rationalContraction_reciprocity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

At the Bakalov–Kac root and nonzero t, the cocycle-weighted contraction equals the weighted contraction on (b,a) at t⁻¹ times t raised to ⟨Na,b⟩. The phase cancellation is an identity of rational functions.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeCocycle.c`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedContraction.scalar_contraction`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedContractionReciprocity.c_mul_rationalContraction_reciprocity`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedContractionReciprocity.c_mul_reciprocityPhase`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedContractionReciprocity.rationalContraction`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedContractionReciprocity.rationalContraction_X_expansion`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedContractionReciprocity.rationalContraction_reciprocity`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedContractionReciprocity.reciprocityPhase`
- Dependency: [D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction](ThirdTwistedChargeAction.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedContraction](ThirdTwistedContraction.md)
