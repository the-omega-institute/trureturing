# Common projective coverings and total Kummer fibers

## Abstract

Common projective coverings and total Kummer fibers.

**Definition 1.1 (Characteristic-zero field context).**

Lean statement: `D5/S3/Factorization/Mordell/FieldKummer.Context`

*Formalization.* `D5/S3/Factorization/Mordell/FieldKummer.Context` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Context packages an arbitrary carrier, field structure, characteristic-zero instance and decidable equality. Every characteristic-zero field supplies these data; classical decidable equality imposes no mathematical restriction. It contains no covering, image or desired-conclusion premise.

**Definition 1.2 (Nonzero twist over a field).**

Lean statement: `D5/S3/Factorization/Mordell/FieldKummer.Twist`

*Formalization.* `D5/S3/Factorization/Mordell/FieldKummer.Twist` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Twist packages a Context, a field element d and the hypothesis d is nonzero. Thus quantifying over Twist is exactly quantifying over every characteristic-zero field and every nonzero d. In particular every nonzero rational D gives d through its field embedding.

**Definition 1.3 (Square representative change data).**

Lean statement: `D5/S3/Factorization/Mordell/FieldKummer.RepresentativeChange`

*Formalization.* `D5/S3/Factorization/Mordell/FieldKummer.RepresentativeChange` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

RepresentativeChange packages a nonzero twist, old and new unit representatives b1,b2 and b1 prime,b2 prime, and units u,v satisfying b1 prime times u squared equals b1 and b2 prime times v squared equals b2. These equalities describe the representative change and assert no solubility or desired image. Equality of squareclasses supplies such unit square witnesses.

**Definition 1.4 (Common tuple with three independent coefficients).**

Lean statement: `D5/S3/Factorization/Mordell/FieldKummer.CommonRep`

*Formalization.* `D5/S3/Factorization/Mordell/FieldKummer.CommonRep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For field units b1,b2 and a third field coefficient b3, CommonRep is a nonzero tuple satisfying the two homogeneous equations with third coefficient b3. The locus is defined without reference to a desired Kummer image.

**Definition 1.5 (Common scaling with independent coefficients).**

Lean statement: `D5/S3/Factorization/Mordell/FieldKummer.CommonRel`

*Formalization.* `D5/S3/Factorization/Mordell/FieldKummer.CommonRel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The same field unit scales every coordinate of the independent-coefficient common locus.

**Definition 1.6 (Independent third representative).**

Lean statement: `D5/S3/Factorization/Mordell/FieldKummer.CommonCovering`

*Formalization.* `D5/S3/Factorization/Mordell/FieldKummer.CommonCovering` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The common projective locus allows any third field unit b3; its equations and quotient are independent of any membership certificate.

**Definition 1.7 (Equivalence under square representative changes).**

Lean statement: `D5/S3/Factorization/Mordell/FieldKummer.changeRepresentatives`

*Formalization.* `D5/S3/Factorization/Mordell/FieldKummer.changeRepresentatives` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

If b1 prime times u squared equals b1 and b2 prime times v squared equals b2, multiplying z1,z2,z3 by u,v,uv respectively defines an equivalence of the entire common projective coverings. Its inverse uses the inverse units. No affine normalization or nonvanishing coordinate assumption is required.

**Theorem 1.8 (Actual point preserved by representative change).**

Lean statement: `D5/S3/Factorization/Mordell/FieldKummer.project_changeRepresentatives`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Mordell/FieldKummer.project_changeRepresentatives` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The representative equivalence preserves the projected actual curve point. The proof includes both the abscissa and ordinate when t is nonzero and the point at infinity when t is zero.

**Definition 1.9 (Third-coefficient normalization).**

Lean statement: `D5/S3/Factorization/Mordell/FieldKummer.normalizeThird`

*Formalization.* `D5/S3/Factorization/Mordell/FieldKummer.normalizeThird` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For b3=b1*b2*w squared, multiplying z3 by w gives an equivalence from the independent-third-coefficient projective covering to the product-normalized covering. The inverse multiplies z3 by the inverse of w. All zero-coordinate and infinity cases remain in the common locus.

**Definition 1.10 (Normalization from the product-one squareclass convention).**

Lean statement: `D5/S3/Factorization/Mordell/FieldKummer.normalizeThirdOfClass`

*Formalization.* `D5/S3/Factorization/Mordell/FieldKummer.normalizeThirdOfClass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The condition [b3]=[b1]+[b2] in additive squareclasses supplies a nonzero unit w with b3=b1*b2*w squared. Choosing this witness gives the full projective normalization equivalence. No quotient injectivity or reflection of squares is used.

**Definition 1.11 (Projection for the independent third representative).**

Lean statement: `D5/S3/Factorization/Mordell/FieldKummer.projectThird`

*Formalization.* `D5/S3/Factorization/Mordell/FieldKummer.projectThird` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

With b3=b1*b2*w squared, projectThird projects after normalization. Its finite abscissa is b1*z1 squared/t squared and its ordinate is b1*b2*w*z1*z2*z3/t cubed. At t=0 it is infinity. Changing the choice of square root changes the corresponding orientation; normalization itself includes every exceptional point.

**Definition 1.12 (Split cubic over a field).**

Lean statement: `D5/S3/Factorization/Mordell/FieldKummer.curve`

*Formalization.* `D5/S3/Factorization/Mordell/FieldKummer.curve` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a field K and d in K, the curve has coefficients a1=a3=a6=0, a2=-10d and a4=-75d squared, so its affine equation is y squared=x(x+5d)(x-15d).

**Theorem 1.13 (Ellipticity).**

Lean statement: `D5/S3/Factorization/Mordell/FieldKummer.curve_is_elliptic`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Mordell/FieldKummer.curve_is_elliptic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every characteristic-zero field K and nonzero d, this curve is elliptic, with discriminant 36000000 times d to the sixth power.

**Definition 1.14 (Ordered roots).**

Lean statement: `D5/S3/Factorization/Mordell/FieldKummer.root`

*Formalization.* `D5/S3/Factorization/Mordell/FieldKummer.root` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The ordered roots are 0,-5d,15d.

**Definition 1.15 (Total coordinate representative).**

Lean statement: `D5/S3/Factorization/Mordell/FieldKummer.descentRep`

*Formalization.* `D5/S3/Factorization/Mordell/FieldKummer.descentRep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The representative at infinity is one. At a finite point it is x-e away from the selected root e, and the cubic derivative 3e squared-20de-75d squared at x=e. The three derivative values are -75d squared,100d squared,300d squared.

**Theorem 1.16 (Addition on all points).**

Lean statement: `D5/S3/Factorization/Mordell/FieldKummer.descentRep_add_square`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Mordell/FieldKummer.descentRep_add_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every characteristic-zero field K, nonzero d, ordered root index i, and actual points P,Q, the product of the total representatives at P,Q,P+Q is a square in K. Secants, tangents, inverses, infinity and vanishing shifted coordinates are included.

**Definition 1.17 (Field squareclasses).**

Lean statement: `D5/S3/Factorization/Mordell/FieldKummer.SquareClass`

*Formalization.* `D5/S3/Factorization/Mordell/FieldKummer.SquareClass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The carrier is field units modulo the range of the square-power group homomorphism. Its additive form represents multiplication of squareclasses as addition. Zero is excluded only from the unit representatives, not from affine or covering coordinates.

**Definition 1.18 (Nonzero descent units).**

Lean statement: `D5/S3/Factorization/Mordell/FieldKummer.descentUnit`

*Formalization.* `D5/S3/Factorization/Mordell/FieldKummer.descentUnit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For nonzero d each total descent representative is a unit, including the derivative replacement at every root.

**Definition 1.19 (Single-coordinate homomorphism).**

Lean statement: `D5/S3/Factorization/Mordell/FieldKummer.coordinate`

*Formalization.* `D5/S3/Factorization/Mordell/FieldKummer.coordinate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For nonzero d and every ordered root index, the total representative defines an additive homomorphism from the actual point group to additive field squareclasses.

**Definition 1.20 (Ordered Kummer homomorphism).**

Lean statement: `D5/S3/Factorization/Mordell/FieldKummer.kummer`

*Formalization.* `D5/S3/Factorization/Mordell/FieldKummer.kummer` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Kummer homomorphism is the ordered pair of coordinates zero and one, corresponding to x and x+5d away from their zeros. Infinity maps to the additive pair (0,0). At T0 its representatives are (-75d squared,5d); at Tminus5d they are (-5d,100d squared); at T15d they are (15d,20d). All actual points are in its domain.

**Theorem 1.21 (The third class).**

Lean statement: `D5/S3/Factorization/Mordell/FieldKummer.descentRep_product_square`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Mordell/FieldKummer.descentRep_product_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The product of all three total representatives at every actual point is a field square. Thus the third class is the sum of the first two classes in additive notation.

**Definition 1.22 (Unit class).**

Lean statement: `D5/S3/Factorization/Mordell/FieldKummer.unitClass`

*Formalization.* `D5/S3/Factorization/Mordell/FieldKummer.unitClass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A field unit gives an element of the additive squareclass group.

**Definition 1.23 (Common homogeneous locus).**

Lean statement: `D5/S3/Factorization/Mordell/FieldKummer.CoveringRep`

*Formalization.* `D5/S3/Factorization/Mordell/FieldKummer.CoveringRep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For units b1,b2, a covering representative is one nonzero tuple (t,z1,z2,z3) satisfying b2*z2 squared-b1*z1 squared=5d*t squared and b1*z1 squared-b1*b2*z3 squared=15d*t squared. No Kummer membership is built into the locus. On this same tuple, addition gives b2*z2 squared-b1*b2*z3 squared=20d*t squared.

**Definition 1.24 (Common projective scaling).**

Lean statement: `D5/S3/Factorization/Mordell/FieldKummer.ProjectiveRel`

*Formalization.* `D5/S3/Factorization/Mordell/FieldKummer.ProjectiveRel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two covering representatives are equivalent exactly when all four coordinates are multiplied by the same field unit.

**Definition 1.25 (Projective two-covering).**

Lean statement: `D5/S3/Factorization/Mordell/FieldKummer.Covering`

*Formalization.* `D5/S3/Factorization/Mordell/FieldKummer.Covering` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The covering is the quotient of the independently defined common homogeneous locus by common nonzero scaling.

**Definition 1.26 (Actual elliptic projection).**

Lean statement: `D5/S3/Factorization/Mordell/FieldKummer.projectRep`

*Formalization.* `D5/S3/Factorization/Mordell/FieldKummer.projectRep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

When t is nonzero the projection has x=b1*z1 squared/t squared and y=b1*b2*z1*z2*z3/t cubed. When t is zero the projection is the point at infinity. The homogeneous equations prove actual curve membership.

**Definition 1.27 (Projection on projective classes).**

Lean statement: `D5/S3/Factorization/Mordell/FieldKummer.project`

*Formalization.* `D5/S3/Factorization/Mordell/FieldKummer.project` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual projected point is independent of common nonzero scaling, including its ordinate, and hence descends to the projective quotient.

**Theorem 1.28 (Exact fiber criterion).**

Lean statement: `D5/S3/Factorization/Mordell/FieldKummer.covering_fiber`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Mordell/FieldKummer.covering_fiber` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every characteristic-zero field K, every nonzero d, units b1,b2 and every actual curve point P, there exists a projective covering point projecting to P if and only if the total Kummer image of P is ([b1],[b2]). The construction includes infinity, every two-torsion root, y=0, t=0, and all permitted vanishing coordinates. It constructs a common tuple and adjusts its sign to match the actual ordinate. Consequently covering nonemptiness is equivalent to membership in the complete Kummer image; it is not a Selmer, Cassels-pairing, rank, generator, denominator, integrality or all-WSS theorem.

## References

- Truth anchor: `D5/S3/Factorization/Mordell/FieldKummer.CommonCovering`
- Truth anchor: `D5/S3/Factorization/Mordell/FieldKummer.CommonRel`
- Truth anchor: `D5/S3/Factorization/Mordell/FieldKummer.CommonRep`
- Truth anchor: `D5/S3/Factorization/Mordell/FieldKummer.Context`
- Truth anchor: `D5/S3/Factorization/Mordell/FieldKummer.Covering`
- Truth anchor: `D5/S3/Factorization/Mordell/FieldKummer.CoveringRep`
- Truth anchor: `D5/S3/Factorization/Mordell/FieldKummer.ProjectiveRel`
- Truth anchor: `D5/S3/Factorization/Mordell/FieldKummer.RepresentativeChange`
- Truth anchor: `D5/S3/Factorization/Mordell/FieldKummer.SquareClass`
- Truth anchor: `D5/S3/Factorization/Mordell/FieldKummer.Twist`
- Truth anchor: `D5/S3/Factorization/Mordell/FieldKummer.changeRepresentatives`
- Truth anchor: `D5/S3/Factorization/Mordell/FieldKummer.coordinate`
- Truth anchor: `D5/S3/Factorization/Mordell/FieldKummer.covering_fiber`
- Truth anchor: `D5/S3/Factorization/Mordell/FieldKummer.curve`
- Truth anchor: `D5/S3/Factorization/Mordell/FieldKummer.curve_is_elliptic`
- Truth anchor: `D5/S3/Factorization/Mordell/FieldKummer.descentRep`
- Truth anchor: `D5/S3/Factorization/Mordell/FieldKummer.descentRep_add_square`
- Truth anchor: `D5/S3/Factorization/Mordell/FieldKummer.descentRep_product_square`
- Truth anchor: `D5/S3/Factorization/Mordell/FieldKummer.descentUnit`
- Truth anchor: `D5/S3/Factorization/Mordell/FieldKummer.kummer`
- Truth anchor: `D5/S3/Factorization/Mordell/FieldKummer.normalizeThird`
- Truth anchor: `D5/S3/Factorization/Mordell/FieldKummer.normalizeThirdOfClass`
- Truth anchor: `D5/S3/Factorization/Mordell/FieldKummer.project`
- Truth anchor: `D5/S3/Factorization/Mordell/FieldKummer.projectRep`
- Truth anchor: `D5/S3/Factorization/Mordell/FieldKummer.projectThird`
- Truth anchor: `D5/S3/Factorization/Mordell/FieldKummer.project_changeRepresentatives`
- Truth anchor: `D5/S3/Factorization/Mordell/FieldKummer.root`
- Truth anchor: `D5/S3/Factorization/Mordell/FieldKummer.unitClass`
