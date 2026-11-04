# The literal balanced multiplier

## Abstract

The literal balanced multiplier

**Definition 1.1 (The literal balanced multiplier).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedPolynomial.balancedPolynomial`

*Formalization.* `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedPolynomial.balancedPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

In the original order s,x,z the multiplier is (s+x)^a0 x^a1 z^a2 s^k (s+x-z)^k (x-z)^k.

**Definition 1.2 (The supported coefficient order).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedPolynomial.balancedRotatedPolynomial`

*Formalization.* `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedPolynomial.balancedRotatedPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Reordering coefficient arguments as s,z,x gives (Z+X)^a0 Z^a1 Y^a2 X^k (X+Z-Y)^k (Z-Y)^k.

**Theorem 1.3 (Finite action and reordering).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedPolynomial.balanced_action_rotate`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedPolynomial.balanced_action_rotate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finite polynomial action commutes with swapping the second and third coefficient arguments. This is an identity of signed coefficient functions.

**Theorem 1.4 (The exact finite clearing expansion).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedPolynomial.balanced_action_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedPolynomial.balanced_action_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Expanding the two difference factors gives j,l from zero through k. The remaining positive factor has exponent a0+k-j and is expanded by its finite binomial theorem. This gives the literal finite clearing used by the balanced canonical channel.

**Theorem 1.5 (Cancellation on the supported chamber).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedPolynomial.balanced_injective`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedPolynomial.balanced_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The polynomial is injective on coefficient functions with a uniform first cutoff and a second cutoff at each fixed first exponent in s,z,x order. The X+Z factor uses the first cutoff. The X+Z-Y factor uses induction through first-coordinate rows and then the current row second cutoff. No x cutoff or domain assumption is required.

## References

- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedPolynomial.balancedPolynomial`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedPolynomial.balancedRotatedPolynomial`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedPolynomial.balanced_action_expansion`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedPolynomial.balanced_action_rotate`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedPolynomial.balanced_injective`
- Dependency: [D5/S3/VertexAlgebra/FormalSeries/ThreeFieldInnerPolynomial](ThreeFieldInnerPolynomial.md)
