# Rational and local Kummer compatibility

## Abstract

Rational and local Kummer compatibility.

**Definition 1.1 (Actual point base change).**

Lean statement: `D5/S3/Factorization/Mordell/LocalKummer.rationalBaseChange`

*Formalization.* `D5/S3/Factorization/Mordell/LocalKummer.rationalBaseChange` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every characteristic-zero field K, rationalBaseChange D is Mathlib point base change from the rational curve to K, transported along the explicit coefficient equalities to y squared=x(x+5d)(x-15d), where d is the image of D. It preserves the actual additive group law and maps an affine point (x,y) to the affine point with both coordinates mapped to K.

**Definition 1.2 (Induced squareclass map).**

Lean statement: `D5/S3/Factorization/Mordell/LocalKummer.classMap`

*Formalization.* `D5/S3/Factorization/Mordell/LocalKummer.classMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The rational-to-field ring homomorphism maps rational units to field units. The square-power subgroup is preserved because the image of a squared unit is the square of its image. QuotientGroup.map therefore induces classMap on additive squareclasses. Neither squareclass-map injectivity nor reflection of squares is assumed or asserted.

**Theorem 1.3 (Rational compatibility).**

Lean statement: `D5/S3/Factorization/Mordell/LocalKummer.rational_naturality`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Mordell/LocalKummer.rational_naturality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every characteristic-zero field K, every nonzero rational D and every actual rational point P, the total field Kummer map of its actual base change equals the ordered pair of induced squareclass maps applied to the delivered RationalKummer.kummer of P. This includes infinity and every root point, and preserves the delivered derivative-at-root convention. These are field-unit squareclasses. The statement specializes to the real field and to the p-adic field for every prime p, with no exclusions at 2,3,5,q,r or primes dividing D or C.

The source pair convention (x,x+5D) normalizes the third representative to the product of the first two. Consequently lambda=(q,1) gives the triple (q,1,q), and mu=(1,q) gives (1,q,q), in each completion through the rational unit map. The common homogeneous equations are imposed on one tuple; individual conic solubility is not substituted for covering solubility.

The rational block clients retain their original R=(5D(L squared+3),25D squared LCF) and S=(-15/C squared,75LF/C cubed), with L squared+3=DC squared and L squared+4=5F squared. Their delivered rational Kummer images ([5],[D]) and ([-15],[5]) pass through classMap by the commuting theorem; rational odd multiples and the original translation remain authoritative. This does not establish any full Selmer group, Cassels pairing, rank bound, original generator, nonsingular subgroup, denominator bound, integral criterion, quartic application or all-WSS conclusion. The mutual-residue hypotheses of theorem 79.1 and mutual-nonresidue hypotheses of theorem 78.1 remain distinct downstream assumptions.

## References

- Truth anchor: `D5/S3/Factorization/Mordell/LocalKummer.classMap`
- Truth anchor: `D5/S3/Factorization/Mordell/LocalKummer.rationalBaseChange`
- Truth anchor: `D5/S3/Factorization/Mordell/LocalKummer.rational_naturality`
- Dependency: [D5/S3/Factorization/Mordell/RationalKummer](RationalKummer.md)
