# Universal Logarithmic Integer-Series Power Closure

## Abstract

Hanna's integer-series closure holds for every positive pointwise power.

Let K be any characteristic-zero field. Every natural sequence index and ordinary degree begins at zero. The arbitrary sequence L takes values in K. The canonical integer and rational embeddings are used; cast(K,z) denotes the integer embedding. No convergence, positivity, support restriction or normalization of L(0) is assumed. The series log(K) is the formal log(1+X), with constant zero and degree-r coefficient (-1)^(r+1)/r for r positive. Division in K is field division. The symbols mk, coeff, subst and factorial denote coefficient assembly, ordinary coefficient extraction, formal substitution and natural factorial. Substitution is legitimate because log(K) has constant coefficient zero.

**Definition 1.1 (The exponential generating series).**

$$\forall K: Type, [\operatorname{Field}\left(K\right)] [\operatorname{CharZero}\left(K\right)], \forall L: \mathbb{N} \to K, \operatorname{egf}\left(L\right) = \operatorname{mk}\left((n: \mathbb{N} \mapsto \frac{\operatorname{L}\left(n\right)}{\operatorname{castNat}\left(K, \operatorname{factorial}\left(n\right)\right)})\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaLogarithmicPowerClosure.egf` (`✓ std3`).

*Citation.* Paul D. Hanna (2009). *Hanna's logarithmic integer-series power closure conjecture*. URL: <https://oeis.org/A167138>.

*Commentary.*

Assemble every exponential coefficient L(n)/n!, including n=0. Characteristic zero makes every factorial denominator nonzero.

**Definition 1.2 (Logarithmic coordinates).**

$$\forall K: Type, [\operatorname{Field}\left(K\right)] [\operatorname{CharZero}\left(K\right)], \forall L: \mathbb{N} \to K, \operatorname{logarithmicTransform}\left(L\right) = \operatorname{subst}\left(\operatorname{egf}\left(L\right), \operatorname{log}\left(K\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaLogarithmicPowerClosure.logarithmicTransform` (`✓ std3`).

*Citation.* Paul D. Hanna (2009). *Hanna's logarithmic integer-series power closure conjecture*. URL: <https://oeis.org/A167138>.

*Commentary.*

Substitute the formal logarithm into the exponential generating series.

**Definition 1.3 (Integral ordinary coefficients).**

$$\forall K: Type, [\operatorname{Field}\left(K\right)] [\operatorname{CharZero}\left(K\right)], \forall f: \operatorname{PowerSeries}\left(K\right), \operatorname{IntegralSeries}\left(f\right) = \forall n: \mathbb{N}, \exists z: \mathbb{Z}, \operatorname{coeff}\left(n, f\right) = \operatorname{cast}\left(K, z\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaLogarithmicPowerClosure.IntegralSeries` (`✓ std3`).

*Citation.* Paul D. Hanna (2009). *Hanna's logarithmic integer-series power closure conjecture*. URL: <https://oeis.org/A167138>.

*Commentary.*

Every ordinary coefficient lies in the canonical image of the integers. The integer can vary with the degree; no sign or size bound is imposed.

**Theorem 1.4 (Hanna's full closure conjecture).**

$$\forall K: Type, [\operatorname{Field}\left(K\right)] [\operatorname{CharZero}\left(K\right)], \forall L: \mathbb{N} \to K, \forall m: \mathbb{N}, (\operatorname{IntegralSeries}\left(\operatorname{logarithmicTransform}\left(L\right)\right)) \implies ((0 < m) \implies (\operatorname{IntegralSeries}\left(\operatorname{logarithmicTransform}\left((n: \mathbb{N} \mapsto \operatorname{L}\left(n\right)^{m})\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/HannaLogarithmicPowerClosure.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a167138-logarithmic-power-closure` (proved) by `D5/S1/Recurrence/Algebraic/HannaLogarithmicPowerClosure.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a167138-logarithmic-power-closure","declaration_gid":"D5/S1/Recurrence/Algebraic/HannaLogarithmicPowerClosure.result","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2009). *Hanna's logarithmic integer-series power closure conjecture*. URL: <https://oeis.org/A167138>.

*Commentary.*

Hanna's same conjecture on A167138, A167139 and A167141 is one question. Integral logarithmic coefficients a reconstruct L(n) as the embedded integer sum T(a,n)=sum_(i<=n) a(i)i!S(n,i), by composing with exp(t)-1. Thus integral values of L are derived from the premise. Put q_i(n)=i!S(n,i). Its product with q_j has logarithmic generating series P_ij=sum_(s<=i) (-1)^(i-s) binomial(i,s)((1+X)^s-1)^j, an integer polynomial. This finite column identity is the factorial-scaled formal form of Boyadzhiev-Frontczak Corollary 3.1. At degree r, only n,i,j at most r contribute: q_i(n)=0 when i>n and log(K)^n has no coefficient below n. The product coefficient is therefore the finite integer sum of a(i)b(j) times coeff(r,P_ij). Binary closure and induction prove every positive power, then the canonical rational map transports the identity into the original K. In degree zero the conclusion retains L(0)^m. The natural positive exponent represents exactly the positive integers.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaLogarithmicPowerClosure.IntegralSeries`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaLogarithmicPowerClosure.egf`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaLogarithmicPowerClosure.logarithmicTransform`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaLogarithmicPowerClosure.result`
- Dependency: [D5/S1/Recurrence/Periodic/IntegralEgfTotientPeriod](../Periodic/IntegralEgfTotientPeriod.md)
- Dependency: [D5/S1/Recurrence/Periodic/ScaledLogColumnPeriodicity](../Periodic/ScaledLogColumnPeriodicity.md)
