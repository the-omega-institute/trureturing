# Cubic Map Nonimage on Actual Golden Blocks

## Abstract

The two canonical points of every positive cubic-block layer have no rational preimage under the explicit cubic map.

**Definition 1.1 (The explicit affine image relation).**

$$\operatorname{CubicIsogenyAffineImage}\left(b, X, Y\right) \iff \exists s, t \in \mathbb{Q}, s \neq 0 \land t^{2} = s^{3} - 27b \land X = \frac{s^{3} - 108b}{9s^{2}} \land Y = \frac{t{s^{3} + 216b}}{27s^{3}}$$

*Formalization.* `D5/S3/Factorization/Mordell/GoldenCubicBlockIsogenyNonimage.CubicIsogenyAffineImage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The source coordinates s,t satisfy t squared equals s cubed minus 27b, with s nonzero. The target coordinates are X=(s cubed minus 108b)/(9s squared) and Y=t(s cubed plus 216b)/(27s cubed). This relation is defined only for finite rational source coordinates with s nonzero.

**Theorem 1.2 (Neither canonical point has a rational affine preimage).**

$$\forall j \in \mathbb{N}, 1 \le j \Rightarrow \neg\operatorname{CubicIsogenyAffineImage}\left(-3\left(d_{j}\right)^{2}, d_{j}c_{j}, d_{j}L_{3^{j}}\right) \land \neg\operatorname{CubicIsogenyAffineImage}\left(125\left(d_{j}\right)^{2}, 5d_{j}c_{j}, 25d_{j}F_{3^{j}}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Mordell/GoldenCubicBlockIsogenyNonimage.actual_block_cubic_isogeny_nonimage` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every j at least one, d_j is the cubefree factor and c_j is the cube-part root of B_j=L_(3^j)^2+3. The negative-twist point has coordinates (d_j c_j,d_j L_(3^j)); the positive-twist point has coordinates (5d_j c_j,25d_j F_(3^j)). Neither belongs to the rational affine image relation at its displayed curve constant.

A prime factor of B_j with cubefree exponent one or two exists because B_j is not a cube. The block congruences exclude the primes two, three and five. At that prime, the target abscissa has valuation e+k and the curve constant has valuation 2e, with e equal to one or two and k nonnegative. The equation s^3=9Xs^2+108b has a unique least valuation among its terms for every integer valuation of s, so it has no nonzero rational solution.

The formal image relation uses the stated affine formulas. A group-homomorphism construction and degree calculation for the global isogeny are not part of this statement.

## References

- Truth anchor: `D5/S3/Factorization/Mordell/GoldenCubicBlockIsogenyNonimage.CubicIsogenyAffineImage`
- Truth anchor: `D5/S3/Factorization/Mordell/GoldenCubicBlockIsogenyNonimage.actual_block_cubic_isogeny_nonimage`
- Dependency: [D5/S3/Factorization/Mordell/GoldenCubicBlockMordellTwists](GoldenCubicBlockMordellTwists.md)
