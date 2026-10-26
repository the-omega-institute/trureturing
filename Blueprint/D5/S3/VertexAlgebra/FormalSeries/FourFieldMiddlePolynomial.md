# Finite middle spectator clearing

## Abstract

Finite middle spectator clearing

**Theorem 1.1 (Literal middle multiplier).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/FourFieldMiddlePolynomial.middle_action_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalSeries/FourFieldMiddlePolynomial.middle_action_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any complex module and arbitrary signed four-variable distribution F in coordinates x,b,z,y, finite polynomial action by x^a0 (b+z)^a1 z^a2 y^a3 (x-b-z)^k (x-z)^k (x-y)^k b^k (b+z-y)^k (z-y)^k equals the explicit middle clearing. Three finite spectator indices p,r,s produce outer exponent e0-a0-3k+p+r+s and balanced bounds a1+p,a2+r,a3+s. Two further finite indices j,l expand the remaining cross factors, followed by the finite positive binomial expansion of b+z. All exponents may be signed. No substitution on a raw distribution or support assumption is used.

**Theorem 1.2 (Original six pair factors).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/FourFieldMiddlePolynomial.clearing_four_middle`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalSeries/FourFieldMiddlePolynomial.clearing_four_middle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original four-field clearing factors into the v,t pair factor and five other pair factors. Their finite convolution evaluates F at x-3k+p+r+s, V-p-k+j, T-r-k+l, y-s-j-l with five signed binomial weights. Clearing the active V,T pair after this convolution equals the original six-pair polynomial action with all four labels fixed. This identity is used on actual canonical products.

## References

- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/FourFieldMiddlePolynomial.clearing_four_middle`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/FourFieldMiddlePolynomial.middle_action_expansion`
- Dependency: [D5/S3/VertexAlgebra/FormalSeries/FourFieldInnerPolynomial](FourFieldInnerPolynomial.md)
- Dependency: [D5/S3/VertexAlgebra/Sectors/LatticeSectorChannelTransport](../Sectors/LatticeSectorChannelTransport.md)
