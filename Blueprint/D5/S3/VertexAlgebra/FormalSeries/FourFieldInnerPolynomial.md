# Literal four-field clearing

## Abstract

Literal four-field clearing

**Theorem 1.1 (Literal four-field clearing).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/FourFieldInnerPolynomial.inner_action_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalSeries/FourFieldInnerPolynomial.inner_action_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any complex module and arbitrary signed four-variable coefficient distribution F, finite Laurent convolution by the full polynomial R equals the five-index finite clearing expression. The polynomial contains the four original monomial factors, the untouched spectator pair, all four spectator-to-inner cross factors and b to the locality order. The five binomial indices expand only finite polynomial factors. The resulting shifts are x-a0-3k+h+p0+q0 and y-a1-2k-h+p1+q1, with inner exponents a2+p0+p1 and a3+q0+q1. This statement neither substitutes a raw distribution nor assumes an iterate identity.

**Theorem 1.2 (All six pair factors).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/FourFieldInnerPolynomial.clearing_four`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalSeries/FourFieldInnerPolynomial.clearing_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The product over all six labelled pairs factors into the inner t-position minus q-position factor and the five remaining cross factors. On arbitrary signed distributions its finite polynomial action is the bivariate inner clearing of the five-index cross convolution. The labels retain their original coordinates.

## References

- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/FourFieldInnerPolynomial.clearing_four`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/FourFieldInnerPolynomial.inner_action_expansion`
- Dependency: [D5/S3/VertexAlgebra/FormalSeries/ThreeFieldPolynomialCovariance](ThreeFieldPolynomialCovariance.md)
