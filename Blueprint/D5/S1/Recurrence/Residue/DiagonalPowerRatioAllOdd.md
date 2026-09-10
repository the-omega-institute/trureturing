# Diagonal Power Ratios and Odd Coefficients

## Abstract

Every coefficient of the normalized series in OEIS A397241 is odd.

The generating equation and oddness conjecture are recorded in hanna2026a397241. Write A for generatingSeries and P(r) for approximation(r). The coefficients a(n), the series A, the approximations P(r), and the comparison series B are over the integers. Indices and exponents are natural numbers. Multipliers such as n-1 are integer subtraction after casting n, as in the Lean declaration.

The operator coeff(n,f) extracts the degree-n coefficient, and mk forms a power series from a coefficient function. The operator map applies a ring homomorphism coefficientwise; intCast(ZMod(2)) denotes Int.castRingHom(ZMod(2)). Both sides of the reduction identity are series over ZMod(2), and the constant function in its right-hand side takes value one in ZMod(2).

**Definition 1.1 (Construction of the integer coefficients).**

$$\begin{aligned}\operatorname{P}\left(0\right) = 1\\\forall r: \mathbb{N}, \operatorname{P}\left(r + 1\right) = \operatorname{mk}\left((k: \mathbb{N} \mapsto \operatorname{if} k \le 1 \operatorname{then} 1 \operatorname{else} \operatorname{coeff}\left(k, \operatorname{P}\left(r\right)\right) - (k \cdot \operatorname{coeff}\left(k, \operatorname{P}\left(r\right)^{k}\right) - (k - 1) \cdot \operatorname{coeff}\left(k, \operatorname{P}\left(r\right)^{k + 1}\right)))\right)\\\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = \operatorname{coeff}\left(n, \operatorname{P}\left(n + 1\right)\right)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Residue/DiagonalPowerRatioAllOdd.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Starting from the constant series one, each approximation fixes coefficients zero and one at one and subtracts the diagonal equation residual at every higher degree. Agreement below degree n implies agreement through degree n after this correction. Thus the displayed diagonal coefficients stabilize.

**Definition 1.2 (The generating series).**

$$A = \operatorname{mk}\left(a\right)$$

*Formalization.* `D5/S1/Recurrence/Residue/DiagonalPowerRatioAllOdd.generatingSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient function a defines the formal integer power series A.

**Theorem 1.3 (The normalized defining equation).**

$$(\operatorname{coeff}\left(0, A\right) = 1) \land ((\operatorname{coeff}\left(1, A\right) = 1) \land (\forall n: \mathbb{N}, (1 < n) \implies (n \cdot \operatorname{coeff}\left(n, A^{n}\right) = (n - 1) \cdot \operatorname{coeff}\left(n, A^{n + 1}\right))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/DiagonalPowerRatioAllOdd.generating_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For unit-constant series agreeing below degree n, the difference of the degree-n coefficients of their m-th powers is m times their degree-n coefficient difference. In the equation residual the multiplier is n squared minus (n-1)(n+1), which is one. Stabilization therefore gives a fixed point of the correction, and its residuals vanish.

**Theorem 1.4 (Uniqueness of the normalized integer series).**

$$\forall B: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{coeff}\left(0, B\right) = 1) \implies ((\operatorname{coeff}\left(1, B\right) = 1) \implies ((\forall n: \mathbb{N}, (1 < n) \implies (n \cdot \operatorname{coeff}\left(n, B^{n}\right) = (n - 1) \cdot \operatorname{coeff}\left(n, B^{n + 1}\right))) \implies (B = A)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/DiagonalPowerRatioAllOdd.generating_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Strong induction on the degree compares any normalized solution B with A. Their residuals vanish, so the multiplier-one identity forces equality of the next coefficient. The two normalization hypotheses start the induction.

**Theorem 1.5 (Evenness of central binomial coefficients).**

$$\forall m: \mathbb{N}, (0 < m) \implies (2 \mid \operatorname{choose}\left(2 \cdot m, m\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/DiagonalPowerRatioAllOdd.central_binom_even` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is Mathlib's two_dvd_centralBinom_of_one_le, expressed using choose.

**Theorem 1.6 (The reduction is the all-ones series).**

$$\operatorname{map}\left(\operatorname{intCast}\left(\operatorname{ZMod}\left(2\right)\right), A\right) = \operatorname{mk}\left((n: \mathbb{N} \mapsto 1)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/DiagonalPowerRatioAllOdd.mod_two_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coefficient of degree n in the (n+1)-st power of the all-ones series is choose(2n,n), which is even for n greater than one. For even n the remaining multiplier vanishes modulo two. For odd n=2m+1 greater than one, the other coefficient is choose(4m+1,2m); Lucas reduction modulo two gives choose(2m,m), which is even. The all-ones series therefore satisfies the reduced equation. The same coefficient induction proves uniqueness over ZMod(2), giving the identity.

**Theorem 1.7 (Hanna's oddness conjecture).**

$$\forall n: \mathbb{N}, \operatorname{Odd}\left(\operatorname{a}\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/DiagonalPowerRatioAllOdd.hanna_conjecture` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a397241-diagonal-power-ratio-all-odd` (proved) by `D5/S1/Recurrence/Residue/DiagonalPowerRatioAllOdd.hanna_conjecture`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a397241-diagonal-power-ratio-all-odd","declaration_gid":"D5/S1/Recurrence/Residue/DiagonalPowerRatioAllOdd.hanna_conjecture","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2026). *OEIS A397241, g.f. with n [x^n] A^n = (n-1) [x^n] A^(n+1), all terms odd*. URL: <https://oeis.org/A397241>.

*Commentary.*

Extracting any coefficient of the reduction identity gives a(n)=1 in ZMod(2). Mathlib's integer-cast criterion identifies this with oddness of the integer a(n), including degrees zero and one.

## References

- Truth anchor: `D5/S1/Recurrence/Residue/DiagonalPowerRatioAllOdd.a`
- Truth anchor: `D5/S1/Recurrence/Residue/DiagonalPowerRatioAllOdd.central_binom_even`
- Truth anchor: `D5/S1/Recurrence/Residue/DiagonalPowerRatioAllOdd.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Residue/DiagonalPowerRatioAllOdd.generating_equation`
- Truth anchor: `D5/S1/Recurrence/Residue/DiagonalPowerRatioAllOdd.generating_unique`
- Truth anchor: `D5/S1/Recurrence/Residue/DiagonalPowerRatioAllOdd.hanna_conjecture`
- Truth anchor: `D5/S1/Recurrence/Residue/DiagonalPowerRatioAllOdd.mod_two_identity`
