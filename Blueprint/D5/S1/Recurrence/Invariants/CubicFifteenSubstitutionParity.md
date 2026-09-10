# Hanna's Cubic Substitution Parity Conjecture

## Abstract

The coefficients of OEIS A392525 are odd exactly at powers of two.

Paul D. Hanna's OEIS A392525 entry gives the functional equation and parity conjecture recorded in hanna2026a392525. Formula (1), A(X)^3 = A(X^3 + 15 X A(X)^3), is used as the defining equation, with constant coefficient zero and linear coefficient one. It is the cubed form of the NAME under this normalization; the cube-root operation itself is not formalized. The separate conjecture modulo ten is not asserted.

PowerSeries(R) is the formal power-series ring with indeterminate X, and subst(f,g) means f composed with g. All powers are ordinary powers. Coefficient indices and exponents are natural numbers. The operator mk constructs a series from its coefficient function, and choose selects a witness of the displayed proved existential proposition. The auxiliary series has coefficients in ZMod(2); generatingSeries and a have integer coefficients.

**Definition 1.1 (The power-of-two series).**

$$\operatorname{powerTwoSeries} = \operatorname{mk}\left((n: \mathbb{N} \mapsto \operatorname{if} (\exists k: \mathbb{N}, n = 2^{k}) \operatorname{then} (1: \operatorname{ZMod}\left(2\right)) \operatorname{else} (0: \operatorname{ZMod}\left(2\right)))\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity.powerTwoSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Coefficient n is one in ZMod(2) precisely when n is a power of two, and is zero otherwise. In particular the constant coefficient is zero and the linear coefficient is one.

**Theorem 1.2 (The characteristic-two cubic identity).**

$$(\operatorname{powerTwoSeries} = X + \operatorname{powerTwoSeries}^{2}) \land (\operatorname{powerTwoSeries}^{3} = \operatorname{subst}\left(\operatorname{powerTwoSeries}, X^{3} + X \cdot \operatorname{powerTwoSeries}^{3}\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity.thue_series_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Frobenius and halving a power-of-two exponent give C = X + C squared. Put t = X cubed + X C cubed. Polynomial algebra shows that C cubed satisfies Y + Y squared = t. Substitution into the quadratic identity shows that C(t) satisfies the same equation. Two solutions u and v with zero constant coefficients satisfy (u-v)(1+u+v)=0. The second factor has constant coefficient one, so absence of zero divisors forces u=v. Here C denotes powerTwoSeries.

**Definition 1.3 (The normalized integer solution).**

$$\operatorname{generatingSeries} = \operatorname{choose}\left(\exists f: \operatorname{PowerSeries}\left(\mathbb{Z}\right), ((\operatorname{constantCoeff}\left(f\right) = 0) \land ((\operatorname{coeff}\left(1, f\right) = 1) \land (f^{3} = \operatorname{subst}\left(f, X^{3} + 15 \cdot X \cdot f^{3}\right))))\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity.generatingSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Starting from X, correct coefficient n by the negative of the degree-(n+2) residual coefficient divided by three using integer division. Modulo three, Frobenius identifies the cube with substitution of X cubed, and the factor fifteen vanishes. Every residual coefficient is therefore divisible by three. Corrections preserve earlier coefficients and remove the next error; their stabilized coefficients prove the displayed existence proposition.

**Definition 1.4 (The integer coefficient sequence).**

$$\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = \operatorname{coeff}\left(n, \operatorname{generatingSeries}\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The value a(n) is coefficient n of the constructed generating series. Its normalization gives a(0)=0 and a(1)=1.

**Theorem 1.5 (The functional equation and normalization).**

$$(\operatorname{constantCoeff}\left(\operatorname{generatingSeries}\right) = 0) \land ((\operatorname{coeff}\left(1, \operatorname{generatingSeries}\right) = 1) \land (\operatorname{generatingSeries}^{3} = \operatorname{subst}\left(\operatorname{generatingSeries}, X^{3} + 15 \cdot X \cdot \operatorname{generatingSeries}^{3}\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity.generating_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The selected witness satisfies both normalization conditions and the exact cubic functional equation of OEIS A392525. The identity holds at every degree by stabilization of the corrected approximations.

**Theorem 1.6 (Uniqueness of the integer solution).**

$$\forall f: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{constantCoeff}\left(f\right) = 0) \implies (\operatorname{coeff}\left(1, f\right) = 1) \implies (f^{3} = \operatorname{subst}\left(f, X^{3} + 15 \cdot X \cdot f^{3}\right)) \implies f = \operatorname{generatingSeries}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity.generating_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For normalized series agreeing below n, their cubes differ at degree n+2 by three times their degree-n coefficient difference. Their substituted right sides agree through degree n+2, since the inner series is divisible by X cubed and its change is divisible by X to the power n+3. The first-difference formula and strong induction prove uniqueness over the integers.

**Theorem 1.7 (The A392525 parity conjecture).**

$$\forall n: \mathbb{N}, (1 \le n) \implies (\operatorname{Odd}\left(\operatorname{a}\left(n\right)\right) \iff (\exists k: \mathbb{N}, n = 2^{k}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity.hanna_conjecture` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a392525-cubic-fifteen-substitution-parity` (proved) by `D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity.hanna_conjecture`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a392525-cubic-fifteen-substitution-parity","declaration_gid":"D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity.hanna_conjecture","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2026). *OEIS A392525, g.f. satisfying A(x)^3 = A(x^3 + 15*x*A(x)^3)*. URL: <https://oeis.org/A392525>.

*Commentary.*

Map the proved integer functional equation into ZMod(2), where fifteen equals one and three is nonzero. The same first-difference argument proves uniqueness there. The characteristic-two identity therefore identifies the mapped generating series with powerTwoSeries. The integer-cast parity equivalence proves the conjecture for every positive index.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity.a`
- Truth anchor: `D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity.generating_equation`
- Truth anchor: `D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity.generating_unique`
- Truth anchor: `D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity.hanna_conjecture`
- Truth anchor: `D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity.powerTwoSeries`
- Truth anchor: `D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity.thue_series_equation`
