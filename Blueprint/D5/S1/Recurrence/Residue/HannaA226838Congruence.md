# Hanna's A226838 congruence

## Abstract

Every factorial-normalized coefficient of the original square-exponent rational EGF has an integral residue witness modulo six.

All series are formal power series over the rationals. The notation natval denotes the natural-to-rational cast, val the integer-to-rational cast, and coeff(n,f) the ordinary coefficient of degree n. The source is exp(sum over m>=1 of X^(m^2)/m^m): the exponent is a square and the denominator is a power, not a factorial. Natural division in innerIntegral is expressed by a floor. No analytic convergence or integrality hypothesis is imposed.

**Definition 1.1 (The literal inner series).**

$$\operatorname{H} = \operatorname{PowerSeries}.\operatorname{mk}\left(n\mapsto \operatorname{finsum}\left((m:\mathbb{N})\mapsto \operatorname{ite}\left(0 < m, \operatorname{coeff}\left(n, \operatorname{monomial}\left(m^{2}, \frac{1}{\operatorname{natval}\left(m\right)^{m}}\right)\right), 0\right)\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Residue/HannaA226838Congruence.H` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2013). *OEIS A226838 — E.g.f.: exp( Sum_{n>=1} x^(n^2) / n^n ).*. URL: <https://oeis.org/A226838>.

*Commentary.*

This is the coefficientwise finsum over every natural m with the guard 0<m. For each degree n, coeff_H bounds its support by m<=n using le_square. Thus this definition represents the original unbounded positive-index formal sum, rather than a truncated generating function.

**Definition 1.2 (The formal exponential).**

$$\operatorname{A} = \operatorname{PowerSeries}.\operatorname{subst}\left(\operatorname{PowerSeries}.\operatorname{exp}\left(\mathbb{Q}\right), \operatorname{H}\right)$$

*Formalization.* `D5/S1/Recurrence/Residue/HannaA226838Congruence.A` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2013). *OEIS A226838 — E.g.f.: exp( Sum_{n>=1} x^(n^2) / n^n ).*. URL: <https://oeis.org/A226838>.

*Commentary.*

The argument order is subst(exp(Q),H), namely substitution of H into exp(Q). The private H_zero supplies constantCoeff(H)=0 before eCoeff_composition is applied.

**Definition 1.3 (The derived natural inner coefficients).**

$$\forall n:\mathbb{N}, \operatorname{innerIntegral}\left(n\right) = \sum_{m=0}^{n} \operatorname{ite}\left(0 < m \land m^{2} = n, \left\lfloor\frac{n!}{m^{m}}\right\rfloor, 0\right)$$

*Formalization.* `D5/S1/Recurrence/Residue/HannaA226838Congruence.innerIntegral` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2013). *OEIS A226838 — E.g.f.: exp( Sum_{n>=1} x^(n^2) / n^n ).*. URL: <https://oeis.org/A226838>.

*Commentary.*

The sum is over range(n+1), hence m=0 through n inclusive; all division here is in Nat. At m>0 and m^2=n, power_dvd_square_factorial gives m^m dividing n!. factorial_ratio uses that divisibility and a nonzero rational denominator to identify the quotient cast with n!/(m:Q)^m. Then eCoeff_H proves that innerIntegral(n), cast to Q, equals n! times coeff(n,H). Integrality is derived, not assumed.

**Theorem 1.4 (The congruence for every natural index).**

$$\forall n:\mathbb{N}, \exists k:\mathbb{Z}, \operatorname{natval}\left(n!\right) \cdot \operatorname{coeff}\left(n, \operatorname{A}\right) = 1 + 6 \cdot \operatorname{val}\left(k\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/HannaA226838Congruence.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a226838-square-egf-mod-six` (proved) by `D5/S1/Recurrence/Residue/HannaA226838Congruence.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a226838-square-egf-mod-six","declaration_gid":"D5/S1/Recurrence/Residue/HannaA226838Congruence.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2013). *OEIS A226838 — E.g.f.: exp( Sum_{n>=1} x^(n^2) / n^n ).*. URL: <https://oeis.org/A226838>.

*Commentary.*

OEIS A226838 revision #14 states: a(n) == 1 (mod 6) (conjecture - valid up to n=1024; if true for n>=0, why?). The existential integer witness proves integrality and the residue simultaneously for every n, including zero. For m>=2, six_power_dvd_square_factorial proves 6*m^m divides (m^2)!, treating m=2 and m=3 directly and using product-factorial divisibility for larger m. inner_mod_six therefore reduces the integral inner coefficient sequence to the identity sequence. The result uses eCoeff_H, H_zero, inner_mod_six and composition_unit_mod_six. The existing IntegralEGFComposition.eCoeff_composition, eCoeff_exp and composition_map, together with the original private QuarticEGFModFour.composition_identity_right, transfer that identity through the integral composition law. The private BourasA363347PrimeMultiplicity.pow_dvd_factorial_mul supplies the factorial divisibility. Only integers are reduced to ZMod(6); there is no rational-to-residue-ring map. The theorem and its nine consumed private helpers are conservatively classified bind-only under the external named open-problem exception; H, A and innerIntegral are definitions earned by result. This is an unbounded symbolic argument, not a bounded enumeration or a certified finite instance, so utility is none. The proof is repository-derived and is not attributed to OEIS. Bounded literature clearance certifies no global novelty. An independent focused reading of Yuta Nishibuchi, A Unified Framework for p-adic Congruences and p-adic Interpolations of Sequences, arXiv:2610.11648v2 (history https://arxiv.org/abs/2610.11648, v2 abstract https://arxiv.org/abs/2610.11648v2, HTML https://arxiv.org/html/2610.11648v2, PDF https://arxiv.org/pdf/2610.11648v2, source archive https://arxiv.org/src/2610.11648v2) established no exact implication for this series in that source. The paper supplies conditional p-adic criteria, but applying them here would require target-specific normalized coefficient valuations or a valid decomposition, the correct period, prime strength, and base-value links for both p=2 and p=3, all-index coverage including zero, and a global integrality bridge to an integer witness. These conditions remain unverified for this series. This reading does not claim that the conditions are false or rule out the method, and it does not establish a global novelty or priority claim. The paper is prior-work context, not the identifier of the OEIS source and not an asserted proof of this conjecture.

## References

- Truth anchor: `D5/S1/Recurrence/Residue/HannaA226838Congruence.A`
- Truth anchor: `D5/S1/Recurrence/Residue/HannaA226838Congruence.H`
- Truth anchor: `D5/S1/Recurrence/Residue/HannaA226838Congruence.innerIntegral`
- Truth anchor: `D5/S1/Recurrence/Residue/HannaA226838Congruence.result`
- Dependency: [D5/S1/Recurrence/Residue/QuarticEGFModFour](QuarticEGFModFour.md)
- Dependency: [D5/S3/Arith/Congruence/BourasA363347PrimeMultiplicity](../../../S3/Arith/Congruence/BourasA363347PrimeMultiplicity.md)
