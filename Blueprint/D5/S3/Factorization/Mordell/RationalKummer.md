# Total rational descent and explicit halving

## Abstract

Total rational descent and explicit halving.

**Definition 1.1 (Split rational cubic).**

Lean statement: `D5/S3/Factorization/Mordell/RationalKummer.curve`

*Formalization.* `D5/S3/Factorization/Mordell/RationalKummer.curve` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every rational D, curve D has coefficients a1=a3=a6=0, a2=-10D and a4=-75D squared. Its affine equation is y squared = x(x+5D)(x-15D).

**Theorem 1.2 (Ellipticity).**

Lean statement: `D5/S3/Factorization/Mordell/RationalKummer.curve_is_elliptic`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Mordell/RationalKummer.curve_is_elliptic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonzero rational D, the displayed curve is elliptic. Its discriminant is 36000000 times D to the sixth power.

**Definition 1.3 (Ordered roots).**

Lean statement: `D5/S3/Factorization/Mordell/RationalKummer.root`

*Formalization.* `D5/S3/Factorization/Mordell/RationalKummer.root` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every rational D, the ordered roots are 0, -5D and 15D.

**Theorem 1.4 (An explicit rational half).**

Lean statement: `D5/S3/Factorization/Mordell/RationalKummer.explicit_half`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Mordell/RationalKummer.explicit_half` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For rational D,x,y,a,b,c with D nonzero, a squared=x, b squared=x+5D, c squared=x-15D and abc=-y, every nonsingular point (x,y) has the rational half (x+ab+ac+bc,-(a+b)(a+c)(b+c)). The conclusion constructs its nonsingularity proof and verifies doubling in the actual rational point group. None of a,b,c is required to be nonzero.

**Definition 1.5 (Total descent representatives).**

Lean statement: `D5/S3/Factorization/Mordell/RationalKummer.descentRep`

*Formalization.* `D5/S3/Factorization/Mordell/RationalKummer.descentRep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every rational D and each of the three ordered roots e, the representative at infinity is 1. At a finite point it is x-e when x differs from e, and 3e squared-20De-75D squared when x=e. Thus the zero-coordinate values are -75D squared, 100D squared and 300D squared, respectively.

**Theorem 1.6 (Addition and square products).**

Lean statement: `D5/S3/Factorization/Mordell/RationalKummer.descentRep_add_square`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Mordell/RationalKummer.descentRep_add_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonzero rational D, every root index i and all actual rational points P,Q, the product of the total representatives at P, Q and P+Q is a rational square. The secant and tangent polynomial identities cover finite nonvertical sums; infinity and inverses complete the remaining cases. Replacing a zero coordinate by the root derivative preserves the square-product identity.

**Definition 1.7 (Rational square classes).**

Lean statement: `D5/S3/Factorization/Mordell/RationalKummer.SquareClass`

*Formalization.* `D5/S3/Factorization/Mordell/RationalKummer.SquareClass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

SquareClass is the existing quotient of rational units by the range of the square-power homomorphism. Zero is not a representative of this quotient.

**Definition 1.8 (Single-coordinate homomorphism).**

Lean statement: `D5/S3/Factorization/Mordell/RationalKummer.coordinate`

*Formalization.* `D5/S3/Factorization/Mordell/RationalKummer.coordinate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every nonzero rational D and ordered root index i, coordinate is an additive homomorphism from the actual rational point group to the additive form of rational units modulo squares. It uses the total nonzero descent representative.

**Definition 1.9 (The ordered Kummer pair).**

Lean statement: `D5/S3/Factorization/Mordell/RationalKummer.kummer`

*Formalization.* `D5/S3/Factorization/Mordell/RationalKummer.kummer` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every nonzero rational D, kummer is the product of coordinates 0 and 1. At an ordinary affine point it is the ordered squareclass pair (x,x+5D). At infinity it is (1,1); the root exceptions use the total representatives.

**Theorem 1.10 (The third coordinate).**

Lean statement: `D5/S3/Factorization/Mordell/RationalKummer.descentRep_product_square`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Mordell/RationalKummer.descentRep_product_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonzero rational D and every actual rational point, the product of all three total descent representatives is a rational square. Consequently the three square classes have product one, and the third class is the product of the first two.

**Theorem 1.11 (The complete doubling kernel).**

Lean statement: `D5/S3/Factorization/Mordell/RationalKummer.kummer_zero_iff_double`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Mordell/RationalKummer.kummer_zero_iff_double` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonzero rational D and every actual rational point P, its Kummer pair is zero if and only if there exists an actual rational point Q with Q+Q=P. The reverse construction chooses the signs of three rational square roots so their product is minus the ordinate, then applies the explicit half formula. Infinity and every two-torsion root are included.

**Theorem 1.12 (Affine squarehood criterion).**

Lean statement: `D5/S3/Factorization/Mordell/RationalKummer.affine_double_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Mordell/RationalKummer.affine_double_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonzero rational D and nonsingular affine point (x,y), a rational doubling preimage exists if and only if x, x+5D and x-15D are rational squares. Squarehood includes zero.

**Definition 1.13 (The class of a nonzero rational).**

Lean statement: `D5/S3/Factorization/Mordell/RationalKummer.classOf`

*Formalization.* `D5/S3/Factorization/Mordell/RationalKummer.classOf` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a nonzero rational a, classOf a is its unit class modulo squares, in additive notation.

**Theorem 1.14 (Block-coordinate images and odd multiples).**

Lean statement: `D5/S3/Factorization/Mordell/RationalKummer.block_kummer_images`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Mordell/RationalKummer.block_kummer_images` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let D,C,L,F be nonzero rational numbers satisfying L squared+3=DC squared and L squared+4=5F squared. Suppose R=(5D(L squared+3),25D squared LCF) and S=(-15/C squared,75LF/C cubed) are actual nonsingular points on the displayed curve. Their Kummer images are ([5],[D]) and ([-15],[5]), respectively. Every integer odd multiple (2n+1)S has the latter image, including negative odd multiples. The proof supplies unit-square witnesses DC, 5F, 1/C and L/C for the four coordinate comparisons.

The image statement retains its two curve-membership hypotheses. The block translation theorem derives those memberships and identifies the translate from the two displayed algebraic identities.

**Theorem 1.15 (The original translation).**

Lean statement: `D5/S3/Factorization/Mordell/RationalKummer.block_translation`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Mordell/RationalKummer.block_translation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let D,C,L,F be rational numbers with C nonzero, L squared+3=DC squared and L squared+4=5F squared. These identities force D nonzero. They construct nonsingularity proofs for R=(5D(L squared+3),25D squared LCF), T0=(0,0) and S=(-15/C squared,75LF/C cubed). In the actual rational point group, R+T0=S. The slope from R to T0 is 5LF/C, and its addition coordinates are exactly those displayed for S.

For an original golden block, take N=3 to the power j with j at least one, L=goldenLucas N and F=Nat.fib N. The existing Lucas discriminant identity gives L squared+4=5F squared because N is odd. The Lucas-Fibonacci bridge gives L positive, and this identity forces F nonzero. A positive integer C and the block equation B=L squared+3=DC squared therefore meet all hypotheses above and of the image theorem. Thus the original R and S have images ([5],[D]) and ([-15],[5]); every integer odd multiple of either has the same image as that point. Here T0 has image ([-3],[5D]), its third coordinate is [-15D], and the three quotient coordinates have product one. The third coordinate at every point is the product of the first two.

These descent statements do not determine a full two-Selmer group, a Cassels pairing, a rational rank, nonsingular reduction subgroups, generators, or denominator and integrality bounds.

## References

- Truth anchor: `D5/S3/Factorization/Mordell/RationalKummer.SquareClass`
- Truth anchor: `D5/S3/Factorization/Mordell/RationalKummer.affine_double_iff`
- Truth anchor: `D5/S3/Factorization/Mordell/RationalKummer.block_kummer_images`
- Truth anchor: `D5/S3/Factorization/Mordell/RationalKummer.block_translation`
- Truth anchor: `D5/S3/Factorization/Mordell/RationalKummer.classOf`
- Truth anchor: `D5/S3/Factorization/Mordell/RationalKummer.coordinate`
- Truth anchor: `D5/S3/Factorization/Mordell/RationalKummer.curve`
- Truth anchor: `D5/S3/Factorization/Mordell/RationalKummer.curve_is_elliptic`
- Truth anchor: `D5/S3/Factorization/Mordell/RationalKummer.descentRep`
- Truth anchor: `D5/S3/Factorization/Mordell/RationalKummer.descentRep_add_square`
- Truth anchor: `D5/S3/Factorization/Mordell/RationalKummer.descentRep_product_square`
- Truth anchor: `D5/S3/Factorization/Mordell/RationalKummer.explicit_half`
- Truth anchor: `D5/S3/Factorization/Mordell/RationalKummer.kummer`
- Truth anchor: `D5/S3/Factorization/Mordell/RationalKummer.kummer_zero_iff_double`
- Truth anchor: `D5/S3/Factorization/Mordell/RationalKummer.root`
