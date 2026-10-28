# Prime Odd-Character Weighted Moments

## Abstract

The boundary logarithm series evaluates the Hurwitz zeta function at zero. The resulting finite L-value identity and the functional equation give prime odd-character nonvanishing.

The results below follow the immutable eight-module CharacterSpecialValue closure of Yao Xu's catalan-lean4 source. They concern complex Dirichlet characters, with ZMod.val as the natural representative. The prime hypothesis is retained in both character statements; no composite induced-character formula follows from it. A real Hurwitz argument is first mapped to the unit additive circle. In the displayed formulas c denotes the source character χ.

Audit status (current evidence): exactly three Reg source-equivalence records are declared_validated: Reg.D5.S3.Analytic.Zeta.CatalanPrimeOddMoment.argumentFamily for D5.S3.Analytic.Zeta.CatalanPrimeOddMoment.arg_one_sub_exp_two_pi; Reg.D5.S3.Analytic.Zeta.CatalanPrimeOddMoment.family for D5.S3.Analytic.Zeta.CatalanPrimeOddMoment.hurwitzZeta_apply_zero_of_mem_Ioo; and Reg.D5.S3.Analytic.Zeta.CatalanPrimeOddMoment.sineFamily for D5.S3.Analytic.Zeta.CatalanPrimeOddMoment.sinZeta_one_eq_of_mem_Ioo. The continuation is open/unknown, with 17 additional unvalidated unfinished audit targets tracked at https://github.com/the-omega-institute/trureturing/issues/17346#issuecomment-6304013114. These three records do not complete the 17 audits and do not establish an inexhaustibility result. The current evidence ceiling is standard axiom closure, not Reg admission completion or a full audit certificate. The archived extension_by_zero consumer failure remains un-restored. Exact remaining exclusions are the composite induced-character weighted-moment identity, strict sign, class-number formula, collision converse, quartic or sextic family conclusions, and broader 21-paper completion.

**Theorem 1.1 (The Hurwitz zero value on the open unit interval).**

$$\forall (t:\mathbb{R}), 0<t \land t<1 \Rightarrow \operatorname{hurwitzZeta}(\operatorname{toUnitAddCircle}(t))(0)=\frac{1}{2}-t$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Zeta/CatalanPrimeOddMoment.hurwitzZeta_apply_zero_of_mem_Ioo` (`✓ std3`). ∎

*Citation.* Yao Xu (2026). *catalan-lean4: CharacterSpecialValue*. URL: <https://github.com/cadamcat/catalan-lean4/blob/3dc9375da48d13751fd291f3ee0fda8fa18be56d/Catalan/Stickelberger/CharacterSpecialValue.lean>.

*Commentary.*

A uniform Dirichlet tail bound permits passage to the boundary value at one. Abel's theorem identifies the exponential series with the negative logarithm. Pairing the arguments t and one minus t gives the sine value, and the odd Hurwitz functional equation gives the displayed value at zero. Here toUnitAddCircle is the canonical map from the real numbers to R/Z; the right side is coerced to the complex numbers.

**Theorem 1.2 (The exact prime weighted representative formula).**

$$\forall (p:\mathbb{N}), [\operatorname{Prime}(p)] \forall (c:\operatorname{DirichletCharacter}(\mathbb{C},p)), c\neq1 \Rightarrow L(0,c)=-\frac{\sum_{a:\operatorname{ZMod}(p)} \operatorname{val}(a) c(a)}{p}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Zeta/CatalanPrimeOddMoment.LFunction_zero_eq_neg_weighted_sum` (`✓ std3`). ∎

*Citation.* Yao Xu (2026). *catalan-lean4: CharacterSpecialValue*. URL: <https://github.com/cadamcat/catalan-lean4/blob/3dc9375da48d13751fd291f3ee0fda8fa18be56d/Catalan/Stickelberger/CharacterSpecialValue.lean>.

*Commentary.*

Expand the Dirichlet L-function as a finite sum of Hurwitz values. The term at zero vanishes, the other representatives lie in the open unit interval after division by p, and the complete sum of a nonprincipal character is zero.

**Theorem 1.3 (The full prime nonprincipal odd-character theorem).**

$$\forall (p:\mathbb{N}), [\operatorname{Prime}(p)] \forall (c:\operatorname{DirichletCharacter}(\mathbb{C},p)), c\neq1 \Rightarrow c(-1)=-1 \Rightarrow \sum_{a:\operatorname{ZMod}(p)} \operatorname{val}(a) c(a)\neq0$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Zeta/CatalanPrimeOddMoment.odd_character_weighted_sum_ne_zero` (`✓ std3`). ∎

*Citation.* Yao Xu (2026). *catalan-lean4: CharacterSpecialValue*. URL: <https://github.com/cadamcat/catalan-lean4/blob/3dc9375da48d13751fd291f3ee0fda8fa18be56d/Catalan/Stickelberger/CharacterSpecialValue.lean>.

*Commentary.*

A nonprincipal character at prime level is primitive. Nonvanishing of the inverse character's L-value at one and the primitive functional equation force a nonzero completed value at zero. Oddness makes the gamma factor at zero equal to one. The finite weighted-sum identity then proves nonvanishing.

**Remark 1.4 (exp_two_pi_norm).**

Lean statement: `D5/S3/Analytic/Zeta/CatalanPrimeOddMoment.exp_two_pi_norm`

*Formalization.* `D5/S3/Analytic/Zeta/CatalanPrimeOddMoment.exp_two_pi_norm` (`✓ std3`).

*Citation.* Yao Xu (2026). *catalan-lean4: CharacterSpecialValue*. URL: <https://github.com/cadamcat/catalan-lean4/blob/3dc9375da48d13751fd291f3ee0fda8fa18be56d/Catalan/Stickelberger/CharacterSpecialValue.lean>.

*Commentary.*

For every real t, the norm of exp(2 pi I t) is one.

**Remark 1.5 (exp_two_pi_ne_one).**

Lean statement: `D5/S3/Analytic/Zeta/CatalanPrimeOddMoment.exp_two_pi_ne_one`

*Formalization.* `D5/S3/Analytic/Zeta/CatalanPrimeOddMoment.exp_two_pi_ne_one` (`✓ std3`).

*Citation.* Yao Xu (2026). *catalan-lean4: CharacterSpecialValue*. URL: <https://github.com/cadamcat/catalan-lean4/blob/3dc9375da48d13751fd291f3ee0fda8fa18be56d/Catalan/Stickelberger/CharacterSpecialValue.lean>.

*Commentary.*

For real t strictly between zero and one, exp(2 pi I t) is not one. The exponential equality criterion would otherwise put an integer strictly between zero and one.

**Remark 1.6 (exp_two_pi_pow).**

Lean statement: `D5/S3/Analytic/Zeta/CatalanPrimeOddMoment.exp_two_pi_pow`

*Formalization.* `D5/S3/Analytic/Zeta/CatalanPrimeOddMoment.exp_two_pi_pow` (`✓ std3`).

*Citation.* Yao Xu (2026). *catalan-lean4: CharacterSpecialValue*. URL: <https://github.com/cadamcat/catalan-lean4/blob/3dc9375da48d13751fd291f3ee0fda8fa18be56d/Catalan/Stickelberger/CharacterSpecialValue.lean>.

*Commentary.*

For every real t and natural n, the nth power of exp(2 pi I t) equals exp(2 pi I t n), with the indicated real and natural values coerced to the complex numbers.

**Remark 1.7 (unit_circle_dirichlet_tail_bound).**

Lean statement: `D5/S3/Analytic/Zeta/CatalanPrimeOddMoment.unit_circle_dirichlet_tail_bound`

*Formalization.* `D5/S3/Analytic/Zeta/CatalanPrimeOddMoment.unit_circle_dirichlet_tail_bound` (`✓ std3`).

*Citation.* Yao Xu (2026). *catalan-lean4: CharacterSpecialValue*. URL: <https://github.com/cadamcat/catalan-lean4/blob/3dc9375da48d13751fd291f3ee0fda8fa18be56d/Catalan/Stickelberger/CharacterSpecialValue.lean>.

*Commentary.*

For complex z of norm one with z not equal to one, every real s at least one and natural M and N with one at most M at most N, the norm of the sum of z^n/n^s over M at most n less than N is at most 4/(M times norm(1-z)). The power n^s is complex power at the coerced real exponent. The empty interval M = N remains in scope.

**Remark 1.8 (hurwitzZeta_zero_eq_sinZeta_one_div_pi).**

Lean statement: `D5/S3/Analytic/Zeta/CatalanPrimeOddMoment.hurwitzZeta_zero_eq_sinZeta_one_div_pi`

*Formalization.* `D5/S3/Analytic/Zeta/CatalanPrimeOddMoment.hurwitzZeta_zero_eq_sinZeta_one_div_pi` (`✓ std3`).

*Citation.* Yao Xu (2026). *catalan-lean4: CharacterSpecialValue*. URL: <https://github.com/cadamcat/catalan-lean4/blob/3dc9375da48d13751fd291f3ee0fda8fa18be56d/Catalan/Stickelberger/CharacterSpecialValue.lean>.

*Commentary.*

For every nonzero a in the unit additive circle, hurwitzZeta(a,0) equals sinZeta(a,1)/pi.

**Remark 1.9 (hurwitzZeta_zero_eq_sine_value_of_mem_Ioo).**

Lean statement: `D5/S3/Analytic/Zeta/CatalanPrimeOddMoment.hurwitzZeta_zero_eq_sine_value_of_mem_Ioo`

*Formalization.* `D5/S3/Analytic/Zeta/CatalanPrimeOddMoment.hurwitzZeta_zero_eq_sine_value_of_mem_Ioo` (`✓ std3`).

*Citation.* Yao Xu (2026). *catalan-lean4: CharacterSpecialValue*. URL: <https://github.com/cadamcat/catalan-lean4/blob/3dc9375da48d13751fd291f3ee0fda8fa18be56d/Catalan/Stickelberger/CharacterSpecialValue.lean>.

*Commentary.*

For every real t strictly between zero and one, the same functional-equation identity holds at the canonical unit-circle image of t.

**Remark 1.10 (cauchySeq_unit_circle_log_partial_sums).**

Lean statement: `D5/S3/Analytic/Zeta/CatalanPrimeOddMoment.cauchySeq_unit_circle_log_partial_sums`

*Formalization.* `D5/S3/Analytic/Zeta/CatalanPrimeOddMoment.cauchySeq_unit_circle_log_partial_sums` (`✓ std3`).

*Citation.* Yao Xu (2026). *catalan-lean4: CharacterSpecialValue*. URL: <https://github.com/cadamcat/catalan-lean4/blob/3dc9375da48d13751fd291f3ee0fda8fa18be56d/Catalan/Stickelberger/CharacterSpecialValue.lean>.

*Commentary.*

For every complex z of norm one with z not equal to one, the partial sums over n less than N of z^(n+1)/(n+1) form a Cauchy sequence in the complex numbers.

**Remark 1.11 (tendsto_unit_circle_log_partial_sums).**

Lean statement: `D5/S3/Analytic/Zeta/CatalanPrimeOddMoment.tendsto_unit_circle_log_partial_sums`

*Formalization.* `D5/S3/Analytic/Zeta/CatalanPrimeOddMoment.tendsto_unit_circle_log_partial_sums` (`✓ std3`).

*Citation.* Yao Xu (2026). *catalan-lean4: CharacterSpecialValue*. URL: <https://github.com/cadamcat/catalan-lean4/blob/3dc9375da48d13751fd291f3ee0fda8fa18be56d/Catalan/Stickelberger/CharacterSpecialValue.lean>.

*Commentary.*

For every complex z of norm one with z not equal to one, the partial sums over n less than N of z^n/n tend, as N tends to infinity, to -log(1-z). The n = 0 summand uses Lean's division-by-zero convention and is zero.

**Remark 1.12 (tendsto_expZeta_one_partial_sums_of_tail_bound).**

Lean statement: `D5/S3/Analytic/Zeta/CatalanPrimeOddMoment.tendsto_expZeta_one_partial_sums_of_tail_bound`

*Formalization.* `D5/S3/Analytic/Zeta/CatalanPrimeOddMoment.tendsto_expZeta_one_partial_sums_of_tail_bound` (`✓ std3`).

*Citation.* Yao Xu (2026). *catalan-lean4: CharacterSpecialValue*. URL: <https://github.com/cadamcat/catalan-lean4/blob/3dc9375da48d13751fd291f3ee0fda8fa18be56d/Catalan/Stickelberger/CharacterSpecialValue.lean>.

*Commentary.*

Assuming the complete uniform tail-bound family stated above, for every real t strictly between zero and one the partial sums of exp(2 pi I t n)/n tend to expZeta(toUnitAddCircle(t),1). The assumption quantifies over all z, s, M and N in the tail-bound statement; it is not a bound at a single chosen phase.

**Remark 1.13 (arg_one_sub_exp_two_pi).**

Lean statement: `D5/S3/Analytic/Zeta/CatalanPrimeOddMoment.arg_one_sub_exp_two_pi`

*Formalization.* `D5/S3/Analytic/Zeta/CatalanPrimeOddMoment.arg_one_sub_exp_two_pi` (`✓ std3`).

*Citation.* Yao Xu (2026). *catalan-lean4: CharacterSpecialValue*. URL: <https://github.com/cadamcat/catalan-lean4/blob/3dc9375da48d13751fd291f3ee0fda8fa18be56d/Catalan/Stickelberger/CharacterSpecialValue.lean>.

*Commentary.*

For every real t strictly between zero and one, arg(1-exp(2 pi I t)) equals pi t - pi/2, using the principal complex argument.

**Remark 1.14 (log_one_sub_exp_two_pi_difference).**

Lean statement: `D5/S3/Analytic/Zeta/CatalanPrimeOddMoment.log_one_sub_exp_two_pi_difference`

*Formalization.* `D5/S3/Analytic/Zeta/CatalanPrimeOddMoment.log_one_sub_exp_two_pi_difference` (`✓ std3`).

*Citation.* Yao Xu (2026). *catalan-lean4: CharacterSpecialValue*. URL: <https://github.com/cadamcat/catalan-lean4/blob/3dc9375da48d13751fd291f3ee0fda8fa18be56d/Catalan/Stickelberger/CharacterSpecialValue.lean>.

*Commentary.*

For every real t strictly between zero and one, -log(1-exp(2 pi I t)) plus log(1-exp(2 pi I (1-t))) equals 2 I pi (1/2-t). Both logarithms use the same principal branch; the reflected argument is exactly one minus t.

**Remark 1.15 (LFunction_zero_ne_zero_of_prime_odd).**

Lean statement: `D5/S3/Analytic/Zeta/CatalanPrimeOddMoment.LFunction_zero_ne_zero_of_prime_odd`

*Formalization.* `D5/S3/Analytic/Zeta/CatalanPrimeOddMoment.LFunction_zero_ne_zero_of_prime_odd` (`✓ std3`).

*Citation.* Yao Xu (2026). *catalan-lean4: CharacterSpecialValue*. URL: <https://github.com/cadamcat/catalan-lean4/blob/3dc9375da48d13751fd291f3ee0fda8fa18be56d/Catalan/Stickelberger/CharacterSpecialValue.lean>.

*Commentary.*

For every prime p and every nonprincipal odd complex Dirichlet character modulo p, its Dirichlet L-function at zero is nonzero.

**Remark 1.16 (LFunction_zero_eq_neg_weighted_sum_of_hurwitz_zero).**

Lean statement: `D5/S3/Analytic/Zeta/CatalanPrimeOddMoment.LFunction_zero_eq_neg_weighted_sum_of_hurwitz_zero`

*Formalization.* `D5/S3/Analytic/Zeta/CatalanPrimeOddMoment.LFunction_zero_eq_neg_weighted_sum_of_hurwitz_zero` (`✓ std3`).

*Citation.* Yao Xu (2026). *catalan-lean4: CharacterSpecialValue*. URL: <https://github.com/cadamcat/catalan-lean4/blob/3dc9375da48d13751fd291f3ee0fda8fa18be56d/Catalan/Stickelberger/CharacterSpecialValue.lean>.

*Commentary.*

Assuming hurwitzZeta(toUnitAddCircle(t),0) = 1/2-t for every real t strictly between zero and one, every prime p and every nonprincipal complex Dirichlet character modulo p satisfy the negative weighted representative-sum formula displayed above. Oddness is not required for this equality.

**Remark 1.17 (tendsto_expZeta_one_partial_sums).**

Lean statement: `D5/S3/Analytic/Zeta/CatalanPrimeOddMoment.tendsto_expZeta_one_partial_sums`

*Formalization.* `D5/S3/Analytic/Zeta/CatalanPrimeOddMoment.tendsto_expZeta_one_partial_sums` (`✓ std3`).

*Citation.* Yao Xu (2026). *catalan-lean4: CharacterSpecialValue*. URL: <https://github.com/cadamcat/catalan-lean4/blob/3dc9375da48d13751fd291f3ee0fda8fa18be56d/Catalan/Stickelberger/CharacterSpecialValue.lean>.

*Commentary.*

For every real t strictly between zero and one, the partial sums of exp(2 pi I t n)/n tend to expZeta(toUnitAddCircle(t),1). This version supplies the proved uniform tail bound, so it has no tail-bound assumption.

**Remark 1.18 (expZeta_one_eq_neg_log).**

Lean statement: `D5/S3/Analytic/Zeta/CatalanPrimeOddMoment.expZeta_one_eq_neg_log`

*Formalization.* `D5/S3/Analytic/Zeta/CatalanPrimeOddMoment.expZeta_one_eq_neg_log` (`✓ std3`).

*Citation.* Yao Xu (2026). *catalan-lean4: CharacterSpecialValue*. URL: <https://github.com/cadamcat/catalan-lean4/blob/3dc9375da48d13751fd291f3ee0fda8fa18be56d/Catalan/Stickelberger/CharacterSpecialValue.lean>.

*Commentary.*

For every real t strictly between zero and one, expZeta(toUnitAddCircle(t),1) equals -log(1-exp(2 pi I t)).

**Remark 1.19 (sinZeta_one_eq_of_mem_Ioo).**

Lean statement: `D5/S3/Analytic/Zeta/CatalanPrimeOddMoment.sinZeta_one_eq_of_mem_Ioo`

*Formalization.* `D5/S3/Analytic/Zeta/CatalanPrimeOddMoment.sinZeta_one_eq_of_mem_Ioo` (`✓ std3`).

*Citation.* Yao Xu (2026). *catalan-lean4: CharacterSpecialValue*. URL: <https://github.com/cadamcat/catalan-lean4/blob/3dc9375da48d13751fd291f3ee0fda8fa18be56d/Catalan/Stickelberger/CharacterSpecialValue.lean>.

*Commentary.*

For every real t strictly between zero and one, sinZeta(toUnitAddCircle(t),1) equals pi times (1/2-t), with real values coerced to the complex numbers.

## References

- Truth anchor: `D5/S3/Analytic/Zeta/CatalanPrimeOddMoment.LFunction_zero_eq_neg_weighted_sum`
- Truth anchor: `D5/S3/Analytic/Zeta/CatalanPrimeOddMoment.LFunction_zero_eq_neg_weighted_sum_of_hurwitz_zero`
- Truth anchor: `D5/S3/Analytic/Zeta/CatalanPrimeOddMoment.LFunction_zero_ne_zero_of_prime_odd`
- Truth anchor: `D5/S3/Analytic/Zeta/CatalanPrimeOddMoment.arg_one_sub_exp_two_pi`
- Truth anchor: `D5/S3/Analytic/Zeta/CatalanPrimeOddMoment.cauchySeq_unit_circle_log_partial_sums`
- Truth anchor: `D5/S3/Analytic/Zeta/CatalanPrimeOddMoment.expZeta_one_eq_neg_log`
- Truth anchor: `D5/S3/Analytic/Zeta/CatalanPrimeOddMoment.exp_two_pi_ne_one`
- Truth anchor: `D5/S3/Analytic/Zeta/CatalanPrimeOddMoment.exp_two_pi_norm`
- Truth anchor: `D5/S3/Analytic/Zeta/CatalanPrimeOddMoment.exp_two_pi_pow`
- Truth anchor: `D5/S3/Analytic/Zeta/CatalanPrimeOddMoment.hurwitzZeta_apply_zero_of_mem_Ioo`
- Truth anchor: `D5/S3/Analytic/Zeta/CatalanPrimeOddMoment.hurwitzZeta_zero_eq_sinZeta_one_div_pi`
- Truth anchor: `D5/S3/Analytic/Zeta/CatalanPrimeOddMoment.hurwitzZeta_zero_eq_sine_value_of_mem_Ioo`
- Truth anchor: `D5/S3/Analytic/Zeta/CatalanPrimeOddMoment.log_one_sub_exp_two_pi_difference`
- Truth anchor: `D5/S3/Analytic/Zeta/CatalanPrimeOddMoment.odd_character_weighted_sum_ne_zero`
- Truth anchor: `D5/S3/Analytic/Zeta/CatalanPrimeOddMoment.sinZeta_one_eq_of_mem_Ioo`
- Truth anchor: `D5/S3/Analytic/Zeta/CatalanPrimeOddMoment.tendsto_expZeta_one_partial_sums`
- Truth anchor: `D5/S3/Analytic/Zeta/CatalanPrimeOddMoment.tendsto_expZeta_one_partial_sums_of_tail_bound`
- Truth anchor: `D5/S3/Analytic/Zeta/CatalanPrimeOddMoment.tendsto_unit_circle_log_partial_sums`
- Truth anchor: `D5/S3/Analytic/Zeta/CatalanPrimeOddMoment.unit_circle_dirichlet_tail_bound`
