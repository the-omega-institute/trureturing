# Outer Laurent and Taylor Evaluation

## Abstract

Finite signed Laurent residue evaluation and Taylor reindexing.

Signed numerator coordinates and independent pair denominators are retained throughout. The three complete outer local-residue-to-Taylor identifications, actual interchange, Lambda zero, arbitrary-first DE-L and all-charge induction are not established by these finite algebraic identities. GroundFirst remains a separate final lifting base.

**Theorem 1.1 (Signed local Laurent coefficients).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockOuterTaylorEvaluation.local_laurent_pair_residue`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockOuterTaylorEvaluation.local_laurent_pair_residue` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Two translated Laurent factors have arbitrary integer powers. A negative local pole index yields a finite binomial convolution; a nonnegative index has zero residue. Only the two nonzero translation constants are required.

**Theorem 1.2 (Three independent poles in the J/A local coordinate).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockOuterTaylorEvaluation.current_source_local_monomial`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockOuterTaylorEvaluation.current_source_local_monomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Currying the original ternary monomial at y=v retains the original signed numerator powers. The three clearing orders remain independent, including the separate spectator order K.

**Theorem 1.3 (Exact current/source local monomial residue).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockOuterTaylorEvaluation.current_source_monomial_residue`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockOuterTaylorEvaluation.current_source_monomial_residue` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

The rational normal form is expanded in the genuine Laurent field and its coefficient at minus one is evaluated. The exponent at the local diagonal may be any integer.

**Theorem 1.4 (Finite Laurent numerator evaluation).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockOuterTaylorEvaluation.current_source_laurent_residue`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockOuterTaylorEvaluation.current_source_laurent_residue` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

The local rational residue of every finite labelled Laurent numerator is the full finite sum of its monomial values. No homogeneity or nonnegative numerator coordinate is assumed.

**Theorem 1.5 (Signed finite convolution).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockOuterTaylorEvaluation.finite_signed_outer_convolution`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockOuterTaylorEvaluation.finite_signed_outer_convolution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Integer diagonal exponents add under finite binomial convolution while an arbitrary original Taylor coefficient sequence is retained.

**Theorem 1.6 (Forward Taylor reindexing).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockOuterTaylorEvaluation.finite_forward_outer_taylor`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockOuterTaylorEvaluation.finite_forward_outer_taylor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Independent natural pole and inner bounds determine a finite signed convolution. Reversing the supported antidiagonal gives the original forward residue weights, including empty negative total degree.

**Theorem 1.7 (Reverse Taylor reindexing).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockOuterTaylorEvaluation.finite_reverse_outer_taylor`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockOuterTaylorEvaluation.finite_reverse_outer_taylor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

The reverse order retains the first Taylor coordinate and gives the corresponding signed residue weights. Total degree is unrestricted and negative degree gives an empty sum.

**Theorem 1.8 (Associated-coordinate Vandermonde contraction).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockOuterTaylorEvaluation.finite_associated_contraction`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockOuterTaylorEvaluation.finite_associated_contraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Triangular finite reindexing and Vandermonde contract the associated Taylor coefficient array with an independent signed pole.

**Theorem 1.9 (Fused Taylor reindexing).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockOuterTaylorEvaluation.finite_left_outer_taylor`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockOuterTaylorEvaluation.finite_left_outer_taylor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

The associated-coordinate cocycle contracts to the original fused Taylor weights. This algebraic identity is separate from evaluation of the complete nested actual Q products.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockOuterTaylorEvaluation.current_source_laurent_residue`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockOuterTaylorEvaluation.current_source_local_monomial`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockOuterTaylorEvaluation.current_source_monomial_residue`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockOuterTaylorEvaluation.finite_associated_contraction`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockOuterTaylorEvaluation.finite_forward_outer_taylor`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockOuterTaylorEvaluation.finite_left_outer_taylor`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockOuterTaylorEvaluation.finite_reverse_outer_taylor`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockOuterTaylorEvaluation.finite_signed_outer_convolution`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockOuterTaylorEvaluation.local_laurent_pair_residue`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockNestedQReadout](LatticeHalfFockNestedQReadout.md)
