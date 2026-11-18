# Hanna A181076 Integrality

## Abstract

Integer coefficients of Hanna's OEIS A181076 formal exponential.

**Definition 1.1 (The rational logarithm).**

$$\operatorname{logarithm} = \operatorname{PowerSeries.mk}\left((fun m: \mathbb{N} \mapsto \operatorname{Finset.sum}\left(\operatorname{Finset.range}\left(m + 1\right), (fun n: \mathbb{N} \mapsto \operatorname{Finset.sum}\left(\operatorname{Finset.range}\left(m + 1\right), (fun k: \mathbb{N} \mapsto if (0 < n \land n + k = m) then \frac{(\operatorname{Nat.choose}\left(n + k - 1, k\right): \mathbb{Q})^{n}}{(n: \mathbb{Q})} else 0)\right))\right))\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaA181076Integrality.logarithm` (`✓ std3`).

*Citation.* Paul D. Hanna (2010). *OEIS A181076 ordinary coefficient integrality conjecture*. URL: <https://oeis.org/A181076>.

*Commentary.*

OEIS A181076, NAME (web entry, no page number): "G.f.: exp( Sum_{n>=1} [ Sum_{k>=0} C(n+k-1,k)^n *x^k ] *x^n/n )." The displayed coefficient formula collects the terms of degree m. The indices and all subtractions are natural numbers; subtraction is truncated at zero. The binomial coefficient is Nat.choose.

**Definition 1.2 (The formal exponential).**

$$\operatorname{A} = \operatorname{PowerSeries.subst}\left(\operatorname{logarithm}, \operatorname{PowerSeries.exp}\left(\mathbb{Q}\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaA181076Integrality.A` (`✓ std3`).

*Citation.* Paul D. Hanna (2010). *OEIS A181076 ordinary coefficient integrality conjecture*. URL: <https://oeis.org/A181076>.

*Commentary.*

OEIS A181076, NAME (web entry, no page number): "G.f.: exp( Sum_{n>=1} [ Sum_{k>=0} C(n+k-1,k)^n *x^k ] *x^n/n )." The exponential is formal over the rationals. PowerSeries.subst takes the inner series as its first argument.

**Definition 1.3 (Integer coefficients).**

$$(\operatorname{claim}) \iff (\forall m: \mathbb{N}, \exists z: \mathbb{Z}, \operatorname{PowerSeries.coeff}\left(m, \operatorname{A}\right) = (z: \mathbb{Q}))$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaA181076Integrality.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2010). *OEIS A181076 ordinary coefficient integrality conjecture*. URL: <https://oeis.org/A181076>.

*Commentary.*

OEIS A181076, first COMMENTS line (web entry, no page number): "Conjecture: this sequence consists entirely of integers." The degree m ranges over all natural numbers, including zero; the integer z may depend on m.

**Theorem 1.4 (Integrality in every degree).**

$$\forall m: \mathbb{N}, \exists z: \mathbb{Z}, \operatorname{PowerSeries.coeff}\left(m, \operatorname{A}\right) = (z: \mathbb{Q})$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/HannaA181076Integrality.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a181076-hanna-integrality` (proved) by `D5/S1/Recurrence/Algebraic/HannaA181076Integrality.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a181076-hanna-integrality","declaration_gid":"D5/S1/Recurrence/Algebraic/HannaA181076Integrality.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2010). *OEIS A181076 ordinary coefficient integrality conjecture*. URL: <https://oeis.org/A181076>.

*Commentary.*

Every ordinary coefficient is an integer, and the constant coefficient is one. Put B(n,k)=binom(n+k-1,k) and F(0,k)=0, F(n,k)=B(n,k)^n for positive n. The original binomial divisibility theorem gives n dividing k*B(n,k); divPower with exponent n-1 therefore gives n dividing k*F(n,k). For every prime p and positive n put q=p^(v_p(n)+1), b=B(n,k), c=B(p*n,p*k). HannaA181074Integrality.negbinomCong, raised to p*n, gives q dividing c^(p*n)-b^(p*n). ZMod.pow_card gives p dividing b^p-b for every integer b, including multiples of p. HannaSelfSubstitutionIntegrality.power_lift at U=b^p, V=b and m=n gives q dividing b^(p*n)-b^n. Adding yields exactly the dilation hypothesis of HannaA181070Integrality.integralGeneric, with exponent p*n at the dilated argument. The theorem applies for all primes, including two, and all k, including zero. HannaA181070Integrality.literalUnbounded identifies the logarithm coefficientwise with its finite diagonal sum. The zero-index totalization contributes zero after rational division and adds no source summand. The logarithm has constant coefficient zero, so substitution into the usual formal exponential is legitimate and gives constant coefficient one. The assertion concerns all ordinary coefficients, without factorial scaling, analytic convergence or a degree bound.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA181076Integrality.A`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA181076Integrality.claim`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA181076Integrality.logarithm`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA181076Integrality.result`
- Dependency: [D5/S1/Recurrence/Algebraic/HannaA181074Integrality](HannaA181074Integrality.md)
- Dependency: [D5/S1/Recurrence/Algebraic/HannaSelfSubstitutionIntegrality](HannaSelfSubstitutionIntegrality.md)
