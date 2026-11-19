# Hanna A181084 Integrality

## Abstract

Integer coefficients of Hanna's OEIS A181084 formal exponential.

**Definition 1.1 (The rational logarithm).**

$$\operatorname{logarithm} = \operatorname{PowerSeries.mk}\left((fun m: \mathbb{N} \mapsto \operatorname{Finset.sum}\left(\operatorname{Finset.range}\left(m + 1\right), (fun n: \mathbb{N} \mapsto \operatorname{Finset.sum}\left(\operatorname{Finset.range}\left(n + 1\right), (fun k: \mathbb{N} \mapsto if (0 < n \land n + k = m) then \frac{(\operatorname{Nat.choose}\left(n, k\right): \mathbb{Q})^{n + k + 1}}{(n: \mathbb{Q})} else 0)\right))\right))\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaA181084Integrality.logarithm` (`✓ std3`).

*Citation.* Paul D. Hanna (2010). *OEIS A181084 integrality conjecture*. URL: <https://oeis.org/A181084>.

*Commentary.*

OEIS A181084, NAME (web entry, no page number): "Expansion of g.f.: exp( Sum_{n>=1} [Sum_{k=0..n} binomial(n,k)^(n+k+1) * x^k] * x^n/n )." The displayed coefficient formula collects the terms of degree m. The indices are natural numbers. The inner range includes both k=0 and k=n, and the exponent is n+k+1. The binomial coefficient is Nat.choose.

**Definition 1.2 (The formal exponential).**

$$\operatorname{A} = \operatorname{PowerSeries.subst}\left(\operatorname{logarithm}, \operatorname{PowerSeries.exp}\left(\mathbb{Q}\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaA181084Integrality.A` (`✓ std3`).

*Citation.* Paul D. Hanna (2010). *OEIS A181084 integrality conjecture*. URL: <https://oeis.org/A181084>.

*Commentary.*

OEIS A181084, NAME (web entry, no page number): "Expansion of g.f.: exp( Sum_{n>=1} [Sum_{k=0..n} binomial(n,k)^(n+k+1) * x^k] * x^n/n )." The exponential is formal over the rationals. PowerSeries.subst takes the inner series as its first argument.

**Definition 1.3 (Integer coefficients).**

$$(\operatorname{claim}) \iff (\forall m: \mathbb{N}, \exists z: \mathbb{Z}, \operatorname{PowerSeries.coeff}\left(m, \operatorname{A}\right) = (z: \mathbb{Q}))$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaA181084Integrality.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2010). *OEIS A181084 integrality conjecture*. URL: <https://oeis.org/A181084>.

*Commentary.*

OEIS A181084, first COMMENTS line (web entry, no page number): "Conjecture: this sequence consists entirely of integers." The degree m ranges over all natural numbers, including zero; the integer z may depend on m.

**Theorem 1.4 (Integrality in every degree).**

$$\forall m: \mathbb{N}, \exists z: \mathbb{Z}, \operatorname{PowerSeries.coeff}\left(m, \operatorname{A}\right) = (z: \mathbb{Q})$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/HannaA181084Integrality.result` (`✓ std3`). ∎

*Resolves.* `Problems/hanna181084` (proved) by `D5/S1/Recurrence/Algebraic/HannaA181084Integrality.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hanna181084","declaration_gid":"D5/S1/Recurrence/Algebraic/HannaA181084Integrality.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2010). *OEIS A181084 integrality conjecture*. URL: <https://oeis.org/A181084>.

*Commentary.*

Every ordinary coefficient is an integer. Set F(n,k)=binomial(n,k)^(n+k+1). The existing HannaA181070Integrality.binomDiv and divPower supply n dividing k F(n,k). Adding n dividing n binomial(n,k) to binomDiv gives n dividing (n+k) binomial(n,k). Applying binomCong and variableExponent with exponent parameter n+k gives F(pn,pk) congruent to F(n,k) modulo p^(v_p(n)+1). The existing literalBounded identifies the whole source logarithm with L F, and integralGeneric proves integrality in every degree, including zero. No factorial coefficient scaling occurs.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA181084Integrality.A`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA181084Integrality.claim`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA181084Integrality.logarithm`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA181084Integrality.result`
- Dependency: [D5/S1/Recurrence/Algebraic/HannaA181070Integrality](HannaA181070Integrality.md)
