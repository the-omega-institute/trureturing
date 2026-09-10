# Negative-Power Diagonals Modulo a Prime

## Abstract

One general theorem proves a congruence clause for each of two negative-power diagonal sequences.

The notes hanna2016a266489 and hanna2026a395833 record Hanna's two generating equations and their respective mod-two and mod-three conjectures. One general theorem implies one clause of each entry. These are two different sequences; no equivalence is asserted.

All parameters, degrees, approximation depths, and exponents are natural numbers; subtraction in these expressions is natural subtraction. The coefficients a(p,n) are integers. Write A(p) for generatingSeries(p) and P(p,d) for its integer-series approximation at depth d. The comparison series B is also over the integers. The symbols 1 and X in a series expression denote the constant series one and the formal variable.

The operator coeff(n,f) extracts a coefficient, mk forms a series from a coefficient function, and subst(f,g) means f composed with g. The expression invOfUnit(f,1) is the formal unit inverse when coeff(0,f)=1, as proved for A(p) and assumed for B. Thus the substitution is exactly A(x/A(x)^e), with e=(p-1)(n-1)+1. Integer divisibility is used below; intCast(p) explicitly casts the natural parameter to an integer.

**Definition 1.1 (The triangular coefficient construction).**

$$\begin{aligned}\forall p: \mathbb{N}, \operatorname{P}\left(p, 0\right) = 1\\\forall p: \mathbb{N}, \forall d: \mathbb{N}, \operatorname{P}\left(p, d + 1\right) = \operatorname{mk}\left((n: \mathbb{N} \mapsto \operatorname{if} (n \le 1) \operatorname{then} 1 \operatorname{else} -(\sum_{j \in \operatorname{range}\left(n\right)} ((\operatorname{coeff}\left(j, \operatorname{P}\left(p, d\right)\right)) \cdot (\operatorname{coeff}\left(n - j, (\operatorname{invOfUnit}\left(\operatorname{P}\left(p, d\right), 1\right))^{((p - 1) \cdot (n - 1) + 1) \cdot (j)}\right)))))\right)\\\forall p: \mathbb{N}, \forall n: \mathbb{N}, \operatorname{a}\left(p, n\right) = \operatorname{coeff}\left(n, \operatorname{P}\left(p, n + 1\right)\right)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Residue/NegativePowerDiagonalModPrime.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Starting with P(p,0)=1, the update sets the first two coefficients to one and solves every higher diagonal equation for its leading coefficient. The summand at j=0 is zero in positive degree. Every positive j below n uses only coefficients below n, including those of the inverse power. Agreement below a degree therefore extends by one degree after each update.

**Definition 1.2 (The integer generating series).**

$$\forall p: \mathbb{N}, \operatorname{A}\left(p\right) = \operatorname{mk}\left((n: \mathbb{N} \mapsto \operatorname{a}\left(p, n\right))\right)$$

*Formalization.* `D5/S1/Recurrence/Residue/NegativePowerDiagonalModPrime.generatingSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The stabilized coefficients form A(p) over the integers.

**Theorem 1.3 (The normalized substitution equation).**

$$\forall p: \mathbb{N}, (\operatorname{coeff}\left(0, \operatorname{A}\left(p\right)\right) = 1) \land ((\operatorname{coeff}\left(1, \operatorname{A}\left(p\right)\right) = 1) \land (\forall n: \mathbb{N}, (1 < n) \implies (\operatorname{coeff}\left(n, \operatorname{subst}\left(\operatorname{A}\left(p\right), (X) \cdot ((\operatorname{invOfUnit}\left(\operatorname{A}\left(p\right), 1\right))^{(p - 1) \cdot (n - 1) + 1})\right)\right) = 0)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/NegativePowerDiagonalModPrime.generating_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coefficient of the substitution is a finite sum through outer degree n. Its degree-n summand is a(p,n), since the inverse power has constant coefficient one. The remaining sum is exactly the triangular update. Stabilization gives a fixed point, hence the stated equation for every n>1.

**Theorem 1.4 (Uniqueness of the normalized solution).**

$$\forall p: \mathbb{N}, \forall B: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{coeff}\left(0, B\right) = 1) \implies ((\operatorname{coeff}\left(1, B\right) = 1) \implies ((\forall n: \mathbb{N}, (1 < n) \implies (\operatorname{coeff}\left(n, \operatorname{subst}\left(B, (X) \cdot ((\operatorname{invOfUnit}\left(B, 1\right))^{(p - 1) \cdot (n - 1) + 1})\right)\right) = 0)) \implies (B = \operatorname{A}\left(p\right))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/NegativePowerDiagonalModPrime.generating_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The equation is equivalent to being a fixed point of the triangular update. The inverse-difference identity preserves agreement below each degree, and the update improves that agreement by one. Induction on the degree therefore identifies B with A(p).

**Theorem 1.5 (The prime-parameter congruence).**

$$\forall p: \mathbb{N}, (\operatorname{Prime}\left(p\right)) \implies (\forall n: \mathbb{N}, (2 \le n) \implies (\operatorname{intCast}\left(p\right) \mid \operatorname{a}\left(p, n\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/NegativePowerDiagonalModPrime.diagonal_conjecture_general` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n=r+1>1 the residual of 1+X is (-1)^r choose(p*r,r), obtained by rescaling the geometric series. Mathlib's choose_mul_right gives the exact identity choose(p*r,r)=p*choose(p*r-1,r-1), so this residual vanishes modulo p. The update commutes with reduction of integer coefficients. Its uniqueness over ZMod(p) identifies the reduction of A(p) with 1+X, whose coefficients above degree one vanish.

**Theorem 1.6 (A266489: congruence clause (C2)).**

$$\forall n: \mathbb{N}, (2 \le n) \implies (2 \mid \operatorname{a}\left(2, n\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/NegativePowerDiagonalModPrime.hanna_conjecture_a266489` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a266489-negative-power-diagonal-mod-two` (proved) by `D5/S1/Recurrence/Residue/NegativePowerDiagonalModPrime.hanna_conjecture_a266489`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a266489-negative-power-diagonal-mod-two","declaration_gid":"D5/S1/Recurrence/Residue/NegativePowerDiagonalModPrime.hanna_conjecture_a266489","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2016). *OEIS A266489, g.f. A(x) satisfies: [x^n] A(x/A(x)^n) = 0 for n>1*. URL: <https://oeis.org/A266489>.

*Commentary.*

At p=2 the exponent (p-1)(n-1)+1 equals n for n>1. The normalized generating equation is therefore that of hanna2016a266489. The general theorem at the prime two proves exactly its clause (C2).

**Theorem 1.7 (A395833: the mod-three clause).**

$$\forall n: \mathbb{N}, (2 \le n) \implies (3 \mid \operatorname{a}\left(3, n\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/NegativePowerDiagonalModPrime.hanna_conjecture_a395833` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a395833-negative-power-diagonal-mod-three` (proved) by `D5/S1/Recurrence/Residue/NegativePowerDiagonalModPrime.hanna_conjecture_a395833`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a395833-negative-power-diagonal-mod-three","declaration_gid":"D5/S1/Recurrence/Residue/NegativePowerDiagonalModPrime.hanna_conjecture_a395833","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2026). *OEIS A395833, g.f. A(x) satisfies [x^n] A(x/A(x)^(2*n-1)) = 0 for n > 1*. URL: <https://oeis.org/A395833>.

*Commentary.*

At p=3 the exponent (p-1)(n-1)+1 equals 2*n-1 for n>1. The normalized generating equation is therefore that of hanna2026a395833. The general theorem at the prime three proves its quoted mod-three clause.

## References

- Truth anchor: `D5/S1/Recurrence/Residue/NegativePowerDiagonalModPrime.a`
- Truth anchor: `D5/S1/Recurrence/Residue/NegativePowerDiagonalModPrime.diagonal_conjecture_general`
- Truth anchor: `D5/S1/Recurrence/Residue/NegativePowerDiagonalModPrime.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Residue/NegativePowerDiagonalModPrime.generating_equation`
- Truth anchor: `D5/S1/Recurrence/Residue/NegativePowerDiagonalModPrime.generating_unique`
- Truth anchor: `D5/S1/Recurrence/Residue/NegativePowerDiagonalModPrime.hanna_conjecture_a266489`
- Truth anchor: `D5/S1/Recurrence/Residue/NegativePowerDiagonalModPrime.hanna_conjecture_a395833`
