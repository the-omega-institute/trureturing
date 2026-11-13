# Hanna A181082 Integrality

## Abstract

Integer coefficients of Hanna's OEIS A181082 formal exponential.

**Definition 1.1 (The rational logarithm).**

$$\operatorname{logarithm} = \operatorname{PowerSeries.mk}\left((fun m: \mathbb{N} \mapsto \operatorname{Finset.sum}\left(\operatorname{Finset.range}\left(m + 1\right), (fun n: \mathbb{N} \mapsto \operatorname{Finset.sum}\left(\operatorname{Finset.range}\left(n + 1\right), (fun k: \mathbb{N} \mapsto if (0 < n \land n + k = m) then \frac{(\operatorname{Nat.choose}\left(n, k\right): \mathbb{Q})^{n + k}}{(n: \mathbb{Q})} else 0)\right))\right))\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaA181082Integrality.logarithm` (`✓ std3`).

*Citation.* Paul D. Hanna (2010). *OEIS A181082 integrality conjecture*. URL: <https://oeis.org/A181082>.

*Commentary.*

OEIS A181082, NAME (web entry, no page number): "Expansion of g.f.: exp( Sum_{n>=1} [Sum_{k=0..n} C(n,k)^(n+k) * x^k] * x^n/n )." The displayed coefficient formula collects the terms of degree m. The indices and the exponent n+k are natural numbers. The binomial coefficient is Nat.choose.

**Definition 1.2 (The formal exponential).**

$$\operatorname{A} = \operatorname{PowerSeries.subst}\left(\operatorname{logarithm}, \operatorname{PowerSeries.exp}\left(\mathbb{Q}\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaA181082Integrality.A` (`✓ std3`).

*Citation.* Paul D. Hanna (2010). *OEIS A181082 integrality conjecture*. URL: <https://oeis.org/A181082>.

*Commentary.*

OEIS A181082, NAME (web entry, no page number): "Expansion of g.f.: exp( Sum_{n>=1} [Sum_{k=0..n} C(n,k)^(n+k) * x^k] * x^n/n )." The exponential is formal over the rationals. PowerSeries.subst takes the inner series as its first argument.

**Definition 1.3 (Integer coefficients).**

$$(\operatorname{claim}) \iff (\forall m: \mathbb{N}, \exists z: \mathbb{Z}, \operatorname{PowerSeries.coeff}\left(m, \operatorname{A}\right) = (z: \mathbb{Q}))$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaA181082Integrality.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2010). *OEIS A181082 integrality conjecture*. URL: <https://oeis.org/A181082>.

*Commentary.*

OEIS A181082, first COMMENTS line (web entry, no page number): "Conjecture: this sequence consists entirely of integers." The degree m ranges over all natural numbers, including zero; the integer z may depend on m.

**Theorem 1.4 (Integrality in every degree).**

$$\forall m: \mathbb{N}, \exists z: \mathbb{Z}, \operatorname{PowerSeries.coeff}\left(m, \operatorname{A}\right) = (z: \mathbb{Q})$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/HannaA181082Integrality.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2010). *OEIS A181082 integrality conjecture*. URL: <https://oeis.org/A181082>.

*Commentary.*

Every ordinary coefficient of the displayed formal exponential is an integer, without a degree cutoff, factorial scaling, positivity or extra hypotheses. The source is Paul D. Hanna's A181082 integrality conjecture, preregistration #30033. The fixed OEIS source is revision 6 at commit de48538e52019dc132e250666b0d677b40045ceb; its SHA256 is c188a5d690604f08247757259908274b40830107aae8998171b674dc76ee1da5. Global literature completeness, priority and originality are unverified.

Parameter correspondence: define F82(0,k)=0 and F82(n,k)=Nat.choose(n,k)^(n+k) for n>0. Apply HannaA181070Integrality.integralGeneric to F82. Its conclusion is coefficientwise integrality of PowerSeries.subst (L F82) (PowerSeries.exp Q), using the existing DoldExponentialIntegrality criterion and existing AINTLIB port. No provider is reproved and no third-party code is copied; the port's provenance and license are in Library/RecurrenceComposition/aintlib2026dieudonnedwork.md.

The first criterion hypothesis is n divides k*F82(n,k) for n>0. HannaA181070Integrality.binomDiv gives n divides k*Nat.choose(n,k); multiply by Nat.choose(n,k)^(n+k-1), since n+k>=1. The private helper div82 is used directly by result.

For the prime-scaling hypothesis fix any prime p, n>0 and k>=0. Put a=padicValNat(p,n), q=p^(a+1), t=n+k, b=Nat.choose(n,k) and B=Nat.choose(p*n,p*k). HannaA181070Integrality.binomCong gives B congruent to b modulo q; taking the power p*t reduces the goal to b^(p*t) congruent to b^t modulo q.

If p divides b, Nat.padicValNat_lt_self gives a<n and hence a+1<=t. Both b^t and b^(p*t) are divisible by q. This includes b=0, with no use of a valuation of zero. Otherwise p and b are coprime. From p^a divides n and n divides k*b, coprime cancellation yields p^a divides k, hence p^a divides t. Write t=p^a*u. Euler's theorem and Nat.totient_prime_pow_succ give b^((p-1)*t) congruent to 1 modulo q. Thus b^(p*t)=b^t*b^((p-1)*t) is congruent to b^t. Every prime, including 2, is covered; so are a=0 and k=0. The private exponent_congruence is consumed by cong82, which is consumed by result.

Finite diagonal equality: in degree m only n<=m and n+k=m contribute. HannaA181070Integrality.literalBounded identifies exactly the source sum with L F82. When k>n, Nat.choose(n,k)=0 and n+k>0; the term vanishes. The n=0 convention is zero. At m=0 the logarithm has coefficient zero, so the ordinary exponential has constant coefficient 1. There is no analytic convergence premise or infinite-sum rearrangement.

Per-declaration shape: div82, exponent_congruence, cong82 and result are bind-only, with no escape witness. Each private helper has the live consumer named above. logarithm, A, claim and F82 are definitions, not proof credit. The direct frozen provider is D5/S1/Recurrence/Algebraic/HannaA181070Integrality with statement_id sha256:3092db66acc6fd1d6f4354d8aefb1d52c3e934f2a8cbf9e86d1bed30e823810b. The proposed admission basis for the sole public result is open-problem-resolution; no global novelty or delivered-resolution claim follows from this exposition.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA181082Integrality.A`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA181082Integrality.claim`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA181082Integrality.logarithm`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA181082Integrality.result`
- Dependency: [D5/S1/Recurrence/Algebraic/HannaA181070Integrality](HannaA181070Integrality.md)
