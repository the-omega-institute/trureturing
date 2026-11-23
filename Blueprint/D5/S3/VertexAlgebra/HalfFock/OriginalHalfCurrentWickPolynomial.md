# The vacuum and the lowering flow

## Abstract

Finite Wick polynomials for half-current lowering

**Definition 1.1 (Surviving oscillator).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentWickPolynomial.creator`

*Formalization.* `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentWickPolynomial.creator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an occurrence of mode m, the coefficient of order k keeps the colour and lowers the mode to m minus k, with its generalized binomial weight.

**Definition 1.2 (Central contraction).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentWickPolynomial.pair`

*Formalization.* `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentWickPolynomial.pair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A pair of occurrences contracts at the sum of their modes plus one, with the Gram entry and the half-current contraction scalar.

**Definition 1.3 (Finite Wick recursion).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentWickPolynomial.word`

*Formalization.* `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentWickPolynomial.word` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At each step the head survives or contracts with a position in the remaining word. The respective terms multiply the recursion on the remaining positions.

**Theorem 1.4 (Normal-order coefficients on the vacuum).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentWickPolynomial.word_coeff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentWickPolynomial.word_coeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every nonnegative order, applying the normal-order coefficient to the vacuum gives the coefficient of the finite Wick polynomial. The induction follows the surviving and contracting branches, using the coefficient convolution for each product.

**Theorem 1.5 (Evaluation by inverse oscillator lowering).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentWickPolynomial.eval_word_eq_lowering`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentWickPolynomial.eval_word_eq_lowering` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a lattice with unit Gram determinant and a bound strictly exceeding the degree, evaluation at any complex parameter equals the finite sum of oscillator-lowering powers on the occurrence monomial, with the factorial coefficient at each order.

## References

- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentWickPolynomial.creator`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentWickPolynomial.eval_word_eq_lowering`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentWickPolynomial.pair`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentWickPolynomial.word`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentWickPolynomial.word_coeff`
- Dependency: [D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport](OriginalHalfCurrentTransport.md)
