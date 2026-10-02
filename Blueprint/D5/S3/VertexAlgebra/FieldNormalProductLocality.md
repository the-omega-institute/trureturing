# Ordered Product Locality

## Abstract

Finite residue cancellation preserves locality for the actual Fock state fields.

The two residue halves have pointwise finite support. Polynomial shifts act on coefficient functions, without a multivariable completion or an assumption of normal-product associativity. Both preservation results are consumed by the unrestricted polynomial Fock state-field construction.

**Theorem 1.1 (The sum of three locality orders suffices).**

Lean statement: `D5/S3/VertexAlgebra/FieldNormalProductLocality.normalMinusOne_locality`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FieldNormalProductLocality.normalMinusOne_locality` (`✓ std3`). ∎

*Citation.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *On axioms for a vertex algebra and locality of quantum fields*. URL: <https://arxiv.org/abs/hep-th/9706118v1>.

*Commentary.*

For three pairwise local fields A, B and C, the ordered minus-one product of A and B is local with C. The sufficient order is the sum of the A-C, B-C and A-B orders, independently of the vector. The residue boundary and binomial cancellation are proved, not assumed.

**Theorem 1.2 (Hasse differentiation preserves locality).**

Lean statement: `D5/S3/VertexAlgebra/FieldNormalProductLocality.dividedDerivative_locality`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FieldNormalProductLocality.dividedDerivative_locality` (`✓ std3`). ∎

*Citation.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *On axioms for a vertex algebra and locality of quantum fields*. URL: <https://arxiv.org/abs/hep-th/9706118v1>.

*Commentary.*

The kth divided derivative increases a sufficient locality order by k. The proof differentiates the annihilating coefficient polynomial, then uses the pinned LaurentSeries derivative-iterate identity and the nonzero complex factorial. No upstream commented sketch is imported.

## References

- Truth anchor: `D5/S3/VertexAlgebra/FieldNormalProductLocality.dividedDerivative_locality`
- Truth anchor: `D5/S3/VertexAlgebra/FieldNormalProductLocality.normalMinusOne_locality`
- Dependency: [D5/S3/VertexAlgebra/FieldNormalProduct](FieldNormalProduct.md)
