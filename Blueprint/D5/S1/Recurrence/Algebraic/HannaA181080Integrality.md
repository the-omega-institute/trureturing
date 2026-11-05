# Hanna A181080 Integrality

## Abstract

Integer coefficients of Hanna's OEIS A181080 formal exponential.

**Definition 1.1 (The rational logarithm).**

$$\operatorname{logarithm} = \operatorname{PowerSeries.mk}\left((fun m: \mathbb{N} \mapsto \operatorname{Finset.sum}\left(\operatorname{Finset.range}\left(m + 1\right), (fun n: \mathbb{N} \mapsto \operatorname{Finset.sum}\left(\operatorname{Finset.range}\left(n + 1\right), (fun k: \mathbb{N} \mapsto if (0 < n \land n + k = m) then \frac{(\operatorname{Nat.choose}\left(n, k\right): \mathbb{Q})^{n - k + 1}}{(n: \mathbb{Q})} else 0)\right))\right))\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaA181080Integrality.logarithm` (`✓ std3`).

*Citation.* Paul D. Hanna (2010). *OEIS A181070, A181074 and A181080 integrality conjectures*. URL: <https://oeis.org/A181070>.

*Commentary.*

OEIS A181080, NAME (web entry, no page number): "Expansion of g.f.: exp( Sum_{n>=1} [Sum_{k=0..n} C(n,k)^(n-k+1) * x^k] * x^n/n )." The displayed coefficient formula collects the terms of degree m. The indices and all subtractions are natural numbers; subtraction is truncated at zero. The binomial coefficient is Nat.choose.

**Definition 1.2 (The formal exponential).**

$$\operatorname{A} = \operatorname{PowerSeries.subst}\left(\operatorname{logarithm}, \operatorname{PowerSeries.exp}\left(\mathbb{Q}\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaA181080Integrality.A` (`✓ std3`).

*Citation.* Paul D. Hanna (2010). *OEIS A181070, A181074 and A181080 integrality conjectures*. URL: <https://oeis.org/A181070>.

*Commentary.*

OEIS A181080, NAME (web entry, no page number): "Expansion of g.f.: exp( Sum_{n>=1} [Sum_{k=0..n} C(n,k)^(n-k+1) * x^k] * x^n/n )." The exponential is formal over the rationals. PowerSeries.subst takes the inner series as its first argument.

**Definition 1.3 (Integer coefficients).**

$$(\operatorname{claim}) \iff (\forall m: \mathbb{N}, \exists z: \mathbb{Z}, \operatorname{PowerSeries.coeff}\left(m, \operatorname{A}\right) = (z: \mathbb{Q}))$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaA181080Integrality.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2010). *OEIS A181070, A181074 and A181080 integrality conjectures*. URL: <https://oeis.org/A181070>.

*Commentary.*

OEIS A181080, first COMMENTS line (web entry, no page number): "Conjecture: this sequence consists entirely of integers." The degree m ranges over all natural numbers, including zero; the integer z may depend on m.

**Theorem 1.4 (Integrality in every degree).**

$$\forall m: \mathbb{N}, \exists z: \mathbb{Z}, \operatorname{PowerSeries.coeff}\left(m, \operatorname{A}\right) = (z: \mathbb{Q})$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/HannaA181080Integrality.result` (`✓ std3`). ∎

*Resolves.* `Problems/hanna181080` (proved) by `D5/S1/Recurrence/Algebraic/HannaA181080Integrality.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hanna181080","declaration_gid":"D5/S1/Recurrence/Algebraic/HannaA181080Integrality.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2010). *OEIS A181070, A181074 and A181080 integrality conjectures*. URL: <https://oeis.org/A181070>.

*Commentary.*

Every coefficient of the displayed formal exponential is an integer. The prime-scaling congruence and diagonal identity reduce the assertion to the Dold exponential integrality criterion.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA181080Integrality.A`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA181080Integrality.claim`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA181080Integrality.logarithm`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA181080Integrality.result`
- Dependency: [D5/S1/Recurrence/Algebraic/HannaA181070Integrality](HannaA181070Integrality.md)
