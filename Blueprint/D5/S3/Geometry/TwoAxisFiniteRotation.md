# Two axis circles and finite rotation words

## Abstract

Exact finite generation by two full axis circles and transport with moving axes.

The vector space is the original real Euclidean three-space. Its Lean carrier is EuclideanSpace over the reals on Fin 3. The coordinate equivalence WithLp.toLp and WithLp.ofLp connects it to the original Fin 3 to real vector carrier; inner products become the original dot product and its norm becomes vnorm. Rotations are actual linear isometric equivalences with determinant one. The argument combines the classical reflection and sphere-connectedness results supplied by Mathlib with an explicit intersection of two latitudes. All products below are finite products of actual orthogonal maps.

**Definition 1.1 (The full circle fixing an axis).**

Lean statement: `D5/S3/Geometry/TwoAxisFiniteRotation.axisCircle`

*Formalization.* `D5/S3/Geometry/TwoAxisFiniteRotation.axisCircle` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a vector a, the axis circle consists of every orthogonal map whose determinant is one and which fixes a. The definition also makes sense for a zero axis, although the generation theorem requires strictly positive Gram determinant for its two axes.

**Definition 1.2 (Allowed finite words).**

Lean statement: `D5/S3/Geometry/TwoAxisFiniteRotation.IsAxisWord`

*Formalization.* `D5/S3/Geometry/TwoAxisFiniteRotation.IsAxisWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every letter of a finite list belongs to the full circle fixing a or to the full circle fixing b. Multiplication is composition, so a product R times S acts by first applying S and then R.

**Definition 1.3 (The algebraic word subgroup).**

Lean statement: `D5/S3/Geometry/TwoAxisFiniteRotation.wordGroup`

*Formalization.* `D5/S3/Geometry/TwoAxisFiniteRotation.wordGroup` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A map belongs to the word subgroup precisely when it equals the product of an allowed finite list. The empty list supplies the identity, concatenation supplies multiplication, and reversing the list of inverse letters supplies inversion.

**Theorem 1.4 (Exact generation of all rotations).**

Lean statement: `D5/S3/Geometry/TwoAxisFiniteRotation.two_axis_finite_word`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/TwoAxisFiniteRotation.two_axis_finite_word` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a and b be arbitrary real three-vectors whose squared inner product is strictly less than the product of their squared norms. Every orthogonal map R of determinant one is the product of a finite list with every letter fixing a or b and having determinant one. Neither axis is required to have unit norm. After normalization, write d for their inner product and q for one minus d squared. For every latitude t between d squared and one, an explicit unit vector has latitude d about b and latitude t about a. Two circle elements therefore reach an entire cap about a. This gives a uniform metric neighborhood in its finite-word orbit. Translating that neighborhood proves the orbit and its complement open in the unit sphere. Connectedness makes the orbit the whole sphere. Finally, after matching R on a, the remaining rotation fixes a and is itself an allowed letter. The conclusion is equality with a finite product, without any limit of words.

**Definition 1.5 (Simultaneous rotation of two inputs).**

Lean statement: `D5/S3/Geometry/TwoAxisFiniteRotation.rotatePair`

*Formalization.* `D5/S3/Geometry/TwoAxisFiniteRotation.rotatePair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A rotation acts on a pair of vector inputs by applying that same rotation to each vector. Scalar coordinates can be held fixed as parameters of the function evaluated on the pair.

**Theorem 1.6 (Fixed outputs under moving-axis transport).**

Lean statement: `D5/S3/Geometry/TwoAxisFiniteRotation.moving_axis_invariance`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/TwoAxisFiniteRotation.moving_axis_invariance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a pair p, two axes a and b with strictly positive Gram determinant, and a function F on vector pairs with any output type. Suppose that at every determinant-one rotated input O p, left rotation by any map in either full circle fixing O a or O b preserves F at that input. Then every determinant-one rotation R satisfies F(R p)=F(p). This is equality of the same outputs; the codomain carries no rotation action and needs no topology. To append a fixed-axis letter g on the right of the accumulated map O, apply the local law to O g O inverse on the left. This conjugate fixes the current axis and takes O p exactly to (O g) p. Induction over an exact finite word proves the stated equality. For a scalar/vector residual this mechanism requires its actual circle laws and transported axes, but no continuity of the residual.

For the original spin-factor residual, fix real scalars s and t and a sign epsilon. The function on vector pairs is F(x,y)=D((s,ofLp x),(t,ofLp y)) minus crossD epsilon at those same original inputs. The original pair is inserted by toLp, and a rotation on raw coordinates is ofLp after R after toLp. At an independent pair with (s,t) nonzero, take w=x cross y and ell=s x+t y, and choose a=ell+epsilon w and b=ell-epsilon w. To apply the transport theorem, the actual local circle laws must hold at every rotated input, and the axes there must be O a and O b. Under those hypotheses the conclusion preserves this same scalar/vector residual for every rotation. The function D remains the same total relation throughout the application.

## References

- Truth anchor: `D5/S3/Geometry/TwoAxisFiniteRotation.IsAxisWord`
- Truth anchor: `D5/S3/Geometry/TwoAxisFiniteRotation.axisCircle`
- Truth anchor: `D5/S3/Geometry/TwoAxisFiniteRotation.moving_axis_invariance`
- Truth anchor: `D5/S3/Geometry/TwoAxisFiniteRotation.rotatePair`
- Truth anchor: `D5/S3/Geometry/TwoAxisFiniteRotation.two_axis_finite_word`
- Truth anchor: `D5/S3/Geometry/TwoAxisFiniteRotation.wordGroup`
