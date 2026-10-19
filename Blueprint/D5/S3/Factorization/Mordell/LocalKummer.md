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

Take distinct natural primes q,r with q mod 24=1, r mod 24=19 and Legendre symbols (5/q)=(5/r)=(q/r)=1, as in theorem 79.1. At either place p=q or p=r, let K be the actual p-adic field, d the characteristic-zero image of the natural product q*r, and qK=Units.mk0(q) using the nonzero natural-prime image in K. The conclusions here are nonemptiness of both FieldKummer.Covering d qK 1 and FieldKummer.Covering d 1 qK at both places. At p=q, qK is a field unit; q is not asserted to be a unit of the p-adic integer ring.

The square roots used below follow from the existing odd-prime Hensel theorem, not from an equation-preserving map out of the residue field. For an integer n with legendreSym p n=1 and p odd, legendreSym.eq_one_iff gives a nonzero residue root a. Its natural representative k=a.val satisfies p dividing k squared-n and p not dividing k. For F=X squared-C(n), PadicInt.norm_int_lt_one_iff_dvd gives norm(F(k))<1, while PadicInt.norm_natCast_eq_one_iff gives norm(2k)=1. Thus the strict derivative-norm hypothesis of hensels_lemma holds. Its root in the p-adic integers maps to a root z squared=n in K by PadicInt.coe_pow and PadicInt.coe_intCast. The representative is used only to form an approximate root; no reverse ring homomorphism from ZMod p is used.

At q, the congruence gives q mod 4=1 and q mod 3=1. The existing legendreSym.quadratic_reciprocity_one_mod_four exchanges (r/q) with the given (q/r), and also exchanges (3/q) with (q/3)=1. The supplementary sign law legendreSym.at_neg_one gives (-1/q)=1. Multiplicativity therefore gives (-5r/q)=(5r/q)=(-15r/q)=1. The odd-prime lift supplies A,B,C in the actual q-adic field with A squared=-5r, B squared=5r and C squared=-15r.

For lambda at q, use the single homogeneous tuple (t,z1,z2,z3)=(1,A,0,2A). Its two defining equations are z2 squared-q*z1 squared=5*q*r*t squared and q*z1 squared-q*z3 squared=15*q*r*t squared; both follow from A squared=-5r. For mu at q, use the single tuple (1,0,B,C): q*z2 squared-z1 squared=5*q*r*t squared and z1 squared-q*z3 squared=15*q*r*t squared follow from the two displayed root equations. Each tuple is nonzero because t=1. These witnesses include zero coordinates and project to root points; no root or two-torsion case is removed.

At r, the given (q/r)=1 and the odd-prime lift supply S in the actual r-adic field with S squared=q. For lambda use (0,1,S,1), and for mu use (0,S,1,1). In each case the two defining equations vanish on both sides because t=0 and S squared=q. The coordinate equal to 1 proves that each tuple is nonzero. These are projective points at infinity, retained by the existing definition rather than normalized to t=1.

Each of these four tuples is a FieldKummer.CoveringRep with product-normalized third coefficient q. Applying Quotient.mk gives the corresponding actual FieldKummer.Covering point. The quotient uses FieldKummer.CommonRel: one nonzero field scalar multiplies all four coordinates together. The two classes may use different tuples, but their equations never use separate conic witnesses or separate scales. The coefficient identity d=q*r is the natural-product cast identity in characteristic zero. No local-square, local-image, norm-witness, residue-point or generic-position hypothesis is added.

This application uses the existing definitions and theorems through parameter substitution, extraction of Hensel roots and algebraic normalization; it adds no mathematical declaration. It establishes exactly the four q/r-place nonemptiness assertions. It supplies neither tangent avoidance nor the exceptional q pairing branch, local conditions at the real place, 2,3,5 or good primes, or a Cassels/quartic/rank conclusion. The full original79.1 and original78.1/78.2 obligations are not covered by these four local assertions.

Under the same original distinct-prime, congruence and Legendre hypotheses, both coverings are also nonempty at each of the four small places: K=the real field, the 2-adic field, the 3-adic field and the 5-adic field. At each place d is exactly the characteristic-zero image of the natural product q*r, and qK=Units.mk0(q) uses the nonzero image of the natural prime q. The eight conclusions are literally Nonempty(FieldKummer.Covering d qK 1) and Nonempty(FieldKummer.Covering d 1 qK), separately at each of these actual fields. No final squarehood, local-image, residue-witness or norm-witness premise is added. The real, 2-adic and 3-adic constructions use only consequences of q being prime and q mod 24=1; the 5-adic construction also uses the given (5/q)=1. The other original hypotheses remain in the application statements.

In the real field, Nat.cast_nonneg gives q at least zero and Real.sq_sqrt supplies S=Real.sqrt(q) with S squared=q. For the three p-adic fields use the integer-coefficient polynomial F=X squared-C(q). Polynomial.aeval_def and the existing evaluation and derivative rules identify F.aeval(a) with a squared-q and F.derivative.aeval(a) with 2a. This evaluates the constant polynomial as well as differentiating F; the derivative-norm comparison below is a strict inequality.

At 2, write q=24k+1, where k is the natural quotient q/24. Then 1-q=-24k is divisible by 2 cubed. PadicInt.norm_int_le_pow_iff_dvd gives norm(1-q) at most 2 to the power -3, or 1/8. PadicInt.norm_p gives norm(2)=1/2. Therefore norm(F(1)) is at most 1/8, strictly less than 1/4=norm(F derivative(1)) squared. Applying hensels_lemma at the p-adic integer 1 supplies a root of F. The strict comparison is established in addition to the divisibility bound; the non-strict bound alone is not the Hensel hypothesis.

At 3, the same identity makes 1-q divisible by 3. PadicInt.norm_int_lt_one_iff_dvd gives norm(F(1))<1, and PadicInt.norm_natCast_eq_one_iff with coprimality of 3 and 2 gives norm(F derivative(1))=1. At 5, q mod 24=1 excludes q=2, so legendreSym.quadratic_reciprocity_one_mod_four with first prime 5 transports the given (5/q)=1 to (q/5)=1. The zero-symbol criterion shows that q has nonzero reduction. Then legendreSym.eq_one_iff supplies a nonzero residue root a. Its natural representative n=a.val has 5 dividing n squared-q and is coprime to 5, by ZMod.natCast_zmod_val and the cast-zero divisibility criterion. The existing p-adic integer norm criteria give norm(F(n))<1 and norm(2n)=1. Thus hensels_lemma applies with a strict derivative-norm inequality at both odd small primes.

For each p=2,3,5, the Hensel root z is in the actual p-adic integer ring and satisfies z squared=q there. Applying the ring coercion to the p-adic number field, with PadicInt.coe_pow and PadicInt.coe_natCast, produces S in K with S squared=q. The residue representative at 5 is used only for the approximate root and its divisibility and coprimality proofs; no equation-preserving section from ZMod 5 into characteristic zero is assumed.

For every one of the four fields, use the one common tuple (t,z1,z2,z3)=(0,1,S,1) for lambda and (0,S,1,1) for mu. For lambda the first equation is S squared-q=0 and the second is q-q=0. For mu the first is q-S squared=0 and the second is S squared-q=0. Both right sides vanish because t=0. A coordinate equal to 1 establishes nonzeroness in each case. These are FieldKummer.CoveringRep witnesses with product-normalized third coefficient q; Quotient.mk supplies the corresponding FieldKummer.Covering points. The existing CommonRel uses one common nonzero field scalar for all four coordinates. The witnesses retain the projective points at infinity and impose both equations on the same tuple.

These eight small-place applications use only existing results, witness extraction and algebraic or arithmetic normalization, and introduce no new mathematical declaration. Together with the preceding q/r exposition they still supply no all-place assembly, good-prime conclusion, tangent avoidance, exceptional q pairing computation, Cassels pairing, quartic-symbol evaluation or rank bound. The original79.1 and original78.1/78.2 conclusions and their generator, denominator, integrality and all-WSS consequences remain outside this application.

The rational block clients retain their original R=(5D(L squared+3),25D squared LCF) and S=(-15/C squared,75LF/C cubed), with L squared+3=DC squared and L squared+4=5F squared. Their delivered rational Kummer images ([5],[D]) and ([-15],[5]) pass through classMap by the commuting theorem; rational odd multiples and the original translation remain authoritative. This does not establish any full Selmer group, Cassels pairing, rank bound, original generator, nonsingular subgroup, denominator bound, integral criterion, quartic application or all-WSS conclusion. The mutual-residue hypotheses of theorem 79.1 and mutual-nonresidue hypotheses of theorem 78.1 remain distinct downstream assumptions.

## References

- Truth anchor: `D5/S3/Factorization/Mordell/LocalKummer.classMap`
- Truth anchor: `D5/S3/Factorization/Mordell/LocalKummer.rationalBaseChange`
- Truth anchor: `D5/S3/Factorization/Mordell/LocalKummer.rational_naturality`
- Dependency: [D5/S3/Factorization/Mordell/RationalKummer](RationalKummer.md)
