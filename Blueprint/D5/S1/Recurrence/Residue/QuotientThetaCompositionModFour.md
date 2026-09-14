# Quotient Theta Composition Modulo Four

## Abstract

The positive coefficients of OEIS A378580 are two modulo four exactly at square degrees.

Paul D. Hanna's entry hanna2025a378580 defines the integer series A by A(x/A(x))=theta_3(x), where theta_3(x) is one plus twice the sum of x^(j^2) over positive integers j. It conjectures that positive square degrees have coefficient two modulo four and all other positive degrees have coefficient divisible by four.

All indices are natural numbers. PowerSeries(Z) is the ring of integer formal power series, X is its indeterminate, coeff(n,F) extracts a coefficient, and mk constructs a series from its coefficient function. In the formulas subst(F,U) means F(U), with the outer series first. IsSquare(n) means that n is the square of a natural number. The map operation applies its ring homomorphism to every coefficient; all remainders in the final formula are integer remainders. The notation invOfUnit(F,1) denotes the formal multiplicative inverse when F has constant coefficient one. The imported thetaSeries is D5.S1.Recurrence.Parity.ThetaSelfCompositionModFour.thetaSeries: its degree-zero coefficient is one, its positive square coefficients are two, and all other coefficients are zero.

**Theorem 1.1 (Inverse agreement below a degree).**

$$\forall R: \operatorname{Type}, (\operatorname{CommRing}\left(R\right)) \implies (\forall d: \mathbb{N}, \forall f: \operatorname{PowerSeries}\left(R\right), \forall g: \operatorname{PowerSeries}\left(R\right), (\operatorname{constantCoeff}\left(f\right) = 1) \implies ((\operatorname{constantCoeff}\left(g\right) = 1) \implies ((\forall k: \mathbb{N}, (k < d) \implies (\operatorname{coeff}\left(k, f\right) = \operatorname{coeff}\left(k, g\right))) \implies (\forall n: \mathbb{N}, (n < d) \implies (\operatorname{coeff}\left(n, \operatorname{invOfUnit}\left(f, 1\right)\right) = \operatorname{coeff}\left(n, \operatorname{invOfUnit}\left(g, 1\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/QuotientThetaCompositionModFour.inverse_agreement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If X^d divides G-F, it divides invOfUnit(F,1)*(G-F)*invOfUnit(G,1). The inverse identities identify that product with the difference of the two inverses. Thus their coefficients agree below d.

**Theorem 1.2 (The triangular quotient comparison).**

$$\forall R: \operatorname{Type}, (\operatorname{CommRing}\left(R\right)) \implies (\forall d: \mathbb{N}, \forall f: \operatorname{PowerSeries}\left(R\right), \forall g: \operatorname{PowerSeries}\left(R\right), (\operatorname{constantCoeff}\left(f\right) = 1) \implies ((\operatorname{constantCoeff}\left(g\right) = 1) \implies ((\forall k: \mathbb{N}, (k < d) \implies (\operatorname{coeff}\left(k, f\right) = \operatorname{coeff}\left(k, g\right))) \implies (\forall n: \mathbb{N}, (n \le d) \implies (\operatorname{coeff}\left(n, \operatorname{subst}\left(f, X \cdot \operatorname{invOfUnit}\left(f, 1\right)\right)\right) - \operatorname{coeff}\left(n, \operatorname{subst}\left(g, X \cdot \operatorname{invOfUnit}\left(g, 1\right)\right)\right) = \operatorname{coeff}\left(n, f\right) - \operatorname{coeff}\left(n, g\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/QuotientThetaCompositionModFour.quotient_triangular` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Inverse agreement makes X*invOfUnit(F,1) and X*invOfUnit(G,1) agree below d+1. Their powers therefore agree there too. In the coefficient sum for the remaining outer difference, terms below n cancel, terms above n vanish, and the degree-n multiplier is one.

**Definition 1.3 (The stabilized integer coefficients).**

$$\begin{aligned}\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = \operatorname{coeff}\left(n, \operatorname{approximation}\left(n + 1\right)\right)\\\operatorname{approximation}\left(0\right) = 1\\\forall d: \mathbb{N}, \operatorname{approximation}\left(d + 1\right) = (\operatorname{thetaSeries} + \operatorname{approximation}\left(d\right)) - \operatorname{subst}\left(\operatorname{approximation}\left(d\right), X \cdot \operatorname{invOfUnit}\left(\operatorname{approximation}\left(d\right), 1\right)\right)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Residue/QuotientThetaCompositionModFour.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The auxiliary approximation starts at one and applies the displayed correction. Each approximation has constant coefficient one. Agreement below degree d improves to agreement below degree d+1, so the diagonal coefficient defines the sequence.

**Definition 1.4 (The integer generating series).**

$$\operatorname{generatingSeries} = \operatorname{mk}\left(\operatorname{a}\right)$$

*Formalization.* `D5/S1/Recurrence/Residue/QuotientThetaCompositionModFour.generatingSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The generating series has coefficient function a.

**Theorem 1.5 (The defining functional equation).**

$$(\operatorname{constantCoeff}\left(\operatorname{generatingSeries}\right) = 1) \land (\operatorname{subst}\left(\operatorname{generatingSeries}, X \cdot \operatorname{invOfUnit}\left(\operatorname{generatingSeries}, 1\right)\right) = \operatorname{thetaSeries})$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/QuotientThetaCompositionModFour.generating_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The quotient triangular comparison shows that the correction improves agreement below d to agreement below d+1. The diagonal coefficients therefore stabilize. The resulting series is a fixed point of the correction, which yields exactly the quotient functional equation.

**Theorem 1.6 (Uniqueness of the integer solution).**

$$\forall B: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{constantCoeff}\left(B\right) = 1) \implies ((\operatorname{subst}\left(B, X \cdot \operatorname{invOfUnit}\left(B, 1\right)\right) = \operatorname{thetaSeries}) \implies (B = \operatorname{generatingSeries}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/QuotientThetaCompositionModFour.generating_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every solution is a fixed point of the correction. Induction on degree using the same contraction proves equality of all coefficients.

**Theorem 1.7 (The full series identity modulo four).**

$$\operatorname{map}\left(\operatorname{intCastRingHom}\left(\operatorname{ZMod}\left(4\right)\right), \operatorname{generatingSeries}\right) = \operatorname{map}\left(\operatorname{intCastRingHom}\left(\operatorname{ZMod}\left(4\right)\right), \operatorname{thetaSeries}\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/QuotientThetaCompositionModFour.mod_four_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write the reduced theta series as T=1+2*S. Since 4=0 in ZMod(4), T*T=1, so invOfUnit(T,1)=T. The imported product generating equation and its modulo-four identity give subst(T,X*T)=T; consequently T also satisfies the quotient equation. Mapping the integer quotient equation preserves both substitution and unit inversion. Quotient uniqueness over ZMod(4) identifies its solution with T.

**Theorem 1.8 (Hanna's A378580 conjecture).**

$$\forall n: \mathbb{N}, (0 < n) \implies ((((\operatorname{a}\left(n\right) \bmod 4 = 2) \iff (\operatorname{IsSquare}\left(n\right))) \land ((\operatorname{a}\left(n\right) \bmod 4 = 0) \iff (\neg (\operatorname{IsSquare}\left(n\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/QuotientThetaCompositionModFour.hanna_conjecture` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a378580-quotient-theta-composition-mod-four` (proved) by `D5/S1/Recurrence/Residue/QuotientThetaCompositionModFour.hanna_conjecture`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a378580-quotient-theta-composition-mod-four","declaration_gid":"D5/S1/Recurrence/Residue/QuotientThetaCompositionModFour.hanna_conjecture","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2025). *OEIS A378580, g.f. A(x) satisfies A(x/A(x)) = theta_3(x)*. URL: <https://oeis.org/A378580>.

*Commentary.*

At positive degree, the theta coefficient is two at a square and zero otherwise. The series identity and the integer-cast remainder equivalence give both biconditionals, as conjectured in hanna2025a378580.

## References

- Truth anchor: `D5/S1/Recurrence/Residue/QuotientThetaCompositionModFour.a`
- Truth anchor: `D5/S1/Recurrence/Residue/QuotientThetaCompositionModFour.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Residue/QuotientThetaCompositionModFour.generating_equation`
- Truth anchor: `D5/S1/Recurrence/Residue/QuotientThetaCompositionModFour.generating_unique`
- Truth anchor: `D5/S1/Recurrence/Residue/QuotientThetaCompositionModFour.hanna_conjecture`
- Truth anchor: `D5/S1/Recurrence/Residue/QuotientThetaCompositionModFour.inverse_agreement`
- Truth anchor: `D5/S1/Recurrence/Residue/QuotientThetaCompositionModFour.mod_four_identity`
- Truth anchor: `D5/S1/Recurrence/Residue/QuotientThetaCompositionModFour.quotient_triangular`
- Dependency: [D5/S1/Recurrence/Parity/ThetaSelfCompositionModFour](../Parity/ThetaSelfCompositionModFour.md)
