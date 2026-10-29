# Hanna's A226839 Congruence

## Abstract

Every factorial-normalized coefficient of Hanna's original triangular-exponent EGF is an integer congruent to one modulo three.

All power series are formal over the rationals. Natural division and subtraction are used in triangular and innerIntegral. The notation val denotes the integer-to-rational cast, natval the natural-to-rational cast, and coeff(n,f) the coefficient of degree n. The source defines H(X)=sum over m>=1 of X^(m*(m+1)/2)/m! and A=exp(H). No analytic convergence hypothesis or integral representation is assumed.

**Definition 1.1 (The literal source exponent).**

$$\forall m:\mathbb{N}, \operatorname{triangular}\left(m\right) = \left\lfloor\frac{m \cdot (m + 1)}{2}\right\rfloor$$

*Formalization.* `D5/S1/Recurrence/Residue/HannaA226839Congruence.triangular` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2013). *OEIS A226839: triangular-exponent exponential generating function*. URL: <https://oeis.org/A226839>.

*Commentary.*

The floor expresses Lean's natural-number division of m*(m+1) by two.

**Definition 1.2 (The original inner series).**

$$\operatorname{H} = \operatorname{PowerSeries}.\operatorname{mk}\left(n\mapsto \operatorname{finsum}\left((m:\mathbb{N})\mapsto \operatorname{ite}\left(0 < m, \operatorname{coeff}\left(n, \operatorname{monomial}\left(\operatorname{triangular}\left(m\right), \frac{1}{\operatorname{natval}\left(m!\right)}\right)\right), 0\right)\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Residue/HannaA226839Congruence.H` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2013). *OEIS A226839: triangular-exponent exponential generating function*. URL: <https://oeis.org/A226839>.

*Commentary.*

This is the literal coefficientwise sum over all natural m with the guard 0<m. The private coeff_H proof bounds the degree-n support by m<=n, so finsum agrees with the original unbounded positive-index formal sum.

**Definition 1.3 (The formal exponential).**

$$\operatorname{A} = \operatorname{PowerSeries}.\operatorname{subst}\left(\operatorname{PowerSeries}.\operatorname{exp}\left(\mathbb{Q}\right), \operatorname{H}\right)$$

*Formalization.* `D5/S1/Recurrence/Residue/HannaA226839Congruence.A` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2013). *OEIS A226839: triangular-exponent exponential generating function*. URL: <https://oeis.org/A226839>.

*Commentary.*

Substitution of H into the rational exponential series represents exp(H). The proof establishes constantCoeff(H)=0 before using the substitution theorem.

**Definition 1.4 (The derived integral inner coefficients).**

$$\forall n:\mathbb{N}, \operatorname{innerIntegral}\left(n\right) = \sum_{m=0}^{n} \operatorname{ite}\left(0 < m \land \operatorname{triangular}\left(m\right) = n, \operatorname{Nat}.\operatorname{ascFactorial}\left(m + 1, n - m\right), 0\right)$$

*Formalization.* `D5/S1/Recurrence/Residue/HannaA226839Congruence.innerIntegral` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2013). *OEIS A226839: triangular-exponent exponential generating function*. URL: <https://oeis.org/A226839>.

*Commentary.*

This natural-valued finite sum is defined over range(n+1). Nat.ascFactorial(m+1,n-m) is the rising factorial with n-m factors, with natural truncated subtraction. At triangular(m)=n it equals n!/m!. The private eCoeff_H proves that this sum, cast to the rationals, equals n! times coeff(n,H); this equality is derived.

**Theorem 1.5 (The congruence at every nonnegative index).**

$$\forall n:\mathbb{N}, \exists k:\mathbb{Z}, \operatorname{natval}\left(n!\right) \cdot \operatorname{coeff}\left(n, \operatorname{A}\right) = 1 + 3 \cdot \operatorname{val}\left(k\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/HannaA226839Congruence.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a226839-triangular-egf-mod-three` (proved) by `D5/S1/Recurrence/Residue/HannaA226839Congruence.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a226839-triangular-egf-mod-three","declaration_gid":"D5/S1/Recurrence/Residue/HannaA226839Congruence.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2013). *OEIS A226839: triangular-exponent exponential generating function*. URL: <https://oeis.org/A226839>.

*Commentary.*

The literal source conjecture is: a(n) == 1 (mod 3) (conjecture - valid up to n=1024; if true for n>=0, why?). The integer witness proves integrality and the residue simultaneously, for every natural n including zero. For m=2 the factorial ratio is three; for m>=3 it contains at least three consecutive factors and is divisible by three. The integral inner coefficients therefore reduce to the identity series. Existing IntegralEGFComposition.eCoeff_composition and composition_map, followed by the original private composition_identity_right from QuarticEGFModFour, give the conclusion. Only integers are reduced to ZMod(3); there is no rational-to-residue-field homomorphism. The source's finite-check report supplies no universal proof. The proof is derived in this repository; the bounded literature screen found no settlement in its stated scope, and establishes neither priority nor the absence of prior work.

## References

- Truth anchor: `D5/S1/Recurrence/Residue/HannaA226839Congruence.A`
- Truth anchor: `D5/S1/Recurrence/Residue/HannaA226839Congruence.H`
- Truth anchor: `D5/S1/Recurrence/Residue/HannaA226839Congruence.innerIntegral`
- Truth anchor: `D5/S1/Recurrence/Residue/HannaA226839Congruence.result`
- Truth anchor: `D5/S1/Recurrence/Residue/HannaA226839Congruence.triangular`
- Dependency: [D5/S1/Recurrence/Residue/QuarticEGFModFour](QuarticEGFModFour.md)
