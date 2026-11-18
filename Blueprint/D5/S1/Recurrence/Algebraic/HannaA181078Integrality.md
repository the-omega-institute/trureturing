# Hanna A181078 Integrality

## Abstract

Integer coefficients of Hanna's OEIS A181078 formal exponential.

**Definition 1.1 (The rational logarithm).**

$$\operatorname{logarithm} = \operatorname{PowerSeries.mk}\left((fun m: \mathbb{N} \mapsto \operatorname{Finset.sum}\left(\operatorname{Finset.range}\left(m + 1\right), (fun n: \mathbb{N} \mapsto \operatorname{Finset.sum}\left(\operatorname{Finset.range}\left(m + 1\right), (fun k: \mathbb{N} \mapsto if (0 < n \land n + k = m) then \frac{(\operatorname{Nat.choose}\left(n + k - 1, k\right): \mathbb{Q})^{n + k - 1}}{(n: \mathbb{Q})} else 0)\right))\right))\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaA181078Integrality.logarithm` (`✓ std3`).

*Citation.* Paul D. Hanna (2010). *OEIS A181070, A181074, A181078 and A181080 integrality conjectures*. URL: <https://oeis.org/A181070>.

*Commentary.*

OEIS A181078, NAME (web entry, no page number): "Expansion of g.f.: exp( Sum_{n>=1} [ Sum_{k>=0} C(n+k-1,k)^(n+k-1) *x^k ] *x^n/n )." The displayed coefficient formula collects the terms of degree m. The indices and all subtractions are natural numbers; subtraction is truncated at zero. The binomial coefficient is Nat.choose.

**Definition 1.2 (The formal exponential).**

$$\operatorname{A} = \operatorname{PowerSeries.subst}\left(\operatorname{logarithm}, \operatorname{PowerSeries.exp}\left(\mathbb{Q}\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaA181078Integrality.A` (`✓ std3`).

*Citation.* Paul D. Hanna (2010). *OEIS A181070, A181074, A181078 and A181080 integrality conjectures*. URL: <https://oeis.org/A181070>.

*Commentary.*

OEIS A181078, NAME (web entry, no page number): "Expansion of g.f.: exp( Sum_{n>=1} [ Sum_{k>=0} C(n+k-1,k)^(n+k-1) *x^k ] *x^n/n )." The exponential is formal over the rationals. PowerSeries.subst takes the inner series as its first argument.

**Definition 1.3 (Integer coefficients).**

$$(\operatorname{claim}) \iff (\forall m: \mathbb{N}, \exists z: \mathbb{Z}, \operatorname{PowerSeries.coeff}\left(m, \operatorname{A}\right) = (z: \mathbb{Q}))$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaA181078Integrality.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2010). *OEIS A181070, A181074, A181078 and A181080 integrality conjectures*. URL: <https://oeis.org/A181070>.

*Commentary.*

OEIS A181078, first COMMENTS line (web entry, no page number): "Conjecture: this sequence consists entirely of integers." The degree m ranges over all natural numbers, including zero; the integer z may depend on m.

**Theorem 1.4 (Integrality in every degree).**

$$\forall m: \mathbb{N}, \exists z: \mathbb{Z}, \operatorname{PowerSeries.coeff}\left(m, \operatorname{A}\right) = (z: \mathbb{Q})$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/HannaA181078Integrality.result` (`✓ std3`). ∎

*Resolves.* `Problems/hanna181078` (proved) by `D5/S1/Recurrence/Algebraic/HannaA181078Integrality.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hanna181078","declaration_gid":"D5/S1/Recurrence/Algebraic/HannaA181078Integrality.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2010). *OEIS A181070, A181074, A181078 and A181080 integrality conjectures*. URL: <https://oeis.org/A181070>.

*Commentary.*

Every coefficient of the displayed formal exponential is an integer. Write s=n+k and b=Nat.choose(s-1,k). Negative-binomial power-series coefficients give n dividing k*b and b(p*n,p*k) congruent to b modulo p^(v_p(n)+1). For n+k=1, the weight is 1^0=1 and n=1. Otherwise n divides k*b^(s-1). If p does not divide b, cancellation gives p^v_p(n) dividing k and s. Euler's theorem modulo p^(v_p(n)+1) identifies b^(p*s-1) with b^(s-1). If p divides b, the identities b(1,k)=b(n,0)=1 force n>=2 and k>=1. Since v_p(n)<n, both exponents are at least v_p(n)+1, so both powers vanish modulo that prime power. These two cases give exactly the prime-scaling hypothesis of HannaA181070Integrality.integralGeneric. The identity literalUnbounded identifies its logarithm with the displayed unrestricted double sum: in degree m, n ranges from 1 to m and k=m-n, without any global upper bound on k. The n=0 term in the generic logarithm is zero by rational division by zero. Thus every ordinary coefficient is integral, including the constant coefficient 1. No analytic convergence, coefficient positivity or factorial rescaling is assumed.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA181078Integrality.A`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA181078Integrality.claim`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA181078Integrality.logarithm`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA181078Integrality.result`
- Dependency: [D5/S1/Recurrence/Algebraic/HannaA181074Integrality](HannaA181074Integrality.md)
