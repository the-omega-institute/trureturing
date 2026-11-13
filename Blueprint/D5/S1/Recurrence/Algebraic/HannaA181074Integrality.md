# Hanna A181074 Integrality

## Abstract

Integer coefficients of Hanna's OEIS A181074 formal exponential.

**Definition 1.1 (The rational logarithm).**

$$\operatorname{logarithm} = \operatorname{PowerSeries.mk}\left((fun m: \mathbb{N} \mapsto \operatorname{Finset.sum}\left(\operatorname{Finset.range}\left(m + 1\right), (fun n: \mathbb{N} \mapsto \operatorname{Finset.sum}\left(\operatorname{Finset.range}\left(m + 1\right), (fun k: \mathbb{N} \mapsto if (0 < n \land n + k = m) then \frac{(\operatorname{Nat.choose}\left(n + k - 1, k\right): \mathbb{Q})^{k + 1}}{(n: \mathbb{Q})} else 0)\right))\right))\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaA181074Integrality.logarithm` (`✓ std3`).

*Citation.* Paul D. Hanna (2010). *OEIS A181070, A181074, A181078 and A181080 integrality conjectures*. URL: <https://oeis.org/A181070>.

*Commentary.*

OEIS A181074, NAME (web entry, no page number): "Expansion of g.f.: exp( Sum_{n>=1} [ Sum_{k>=0} C(n+k-1,k)^(k+1) *x^k ] *x^n/n )." The displayed coefficient formula collects the terms of degree m. The indices and all subtractions are natural numbers; subtraction is truncated at zero. The binomial coefficient is Nat.choose.

**Definition 1.2 (The formal exponential).**

$$\operatorname{A} = \operatorname{PowerSeries.subst}\left(\operatorname{logarithm}, \operatorname{PowerSeries.exp}\left(\mathbb{Q}\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaA181074Integrality.A` (`✓ std3`).

*Citation.* Paul D. Hanna (2010). *OEIS A181070, A181074, A181078 and A181080 integrality conjectures*. URL: <https://oeis.org/A181070>.

*Commentary.*

OEIS A181074, NAME (web entry, no page number): "Expansion of g.f.: exp( Sum_{n>=1} [ Sum_{k>=0} C(n+k-1,k)^(k+1) *x^k ] *x^n/n )." The exponential is formal over the rationals. PowerSeries.subst takes the inner series as its first argument.

**Definition 1.3 (Integer coefficients).**

$$(\operatorname{claim}) \iff (\forall m: \mathbb{N}, \exists z: \mathbb{Z}, \operatorname{PowerSeries.coeff}\left(m, \operatorname{A}\right) = (z: \mathbb{Q}))$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaA181074Integrality.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2010). *OEIS A181070, A181074, A181078 and A181080 integrality conjectures*. URL: <https://oeis.org/A181070>.

*Commentary.*

OEIS A181074, first COMMENTS line (web entry, no page number): "Conjecture: this sequence consists entirely of integers." The degree m ranges over all natural numbers, including zero; the integer z may depend on m.

**Lemma 1.4 (Negative-binomial divisibility).**

$$\forall n: \mathbb{N}, \forall k: \mathbb{N}, n \ne 0 \Rightarrow n \mid k \cdot \operatorname{Nat.choose}\left(n + k - 1, k\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/HannaA181074Integrality.negbinomDiv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2010). *OEIS A181070, A181074, A181078 and A181080 integrality conjectures*. URL: <https://oeis.org/A181070>.

*Commentary.*

For every nonzero natural n and every natural k, n divides k times Nat.choose(n+k-1,k). The coefficient of degree k in (sum_j x^j)^n is this binomial coefficient; coefficientDivisibility supplies the divisibility.

**Lemma 1.5 (Prime scaling of negative binomials).**

$$\forall p: \mathbb{N}, \forall n: \mathbb{N}, \forall k: \mathbb{N}, \operatorname{Nat.Prime}\left(p\right) \Rightarrow \left(n \ne 0 \Rightarrow \operatorname{Nat.ModEq}\left(p^{\operatorname{padicValNat}\left(p, n\right) + 1}, \operatorname{Nat.choose}\left(p \cdot n + p \cdot k - 1, p \cdot k\right), \operatorname{Nat.choose}\left(n + k - 1, k\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/HannaA181074Integrality.negbinomCong` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2010). *OEIS A181070, A181074, A181078 and A181080 integrality conjectures*. URL: <https://oeis.org/A181070>.

*Commentary.*

For every prime p, nonzero natural n and natural k, Nat.choose(p*n+p*k-1,p*k) and Nat.choose(n+k-1,k) are congruent modulo p^(padicValNat(p,n)+1). Applying coeffLift to sum_j x^j gives the congruence at the same unrestricted indices.

**Theorem 1.6 (Integrality in every degree).**

$$\forall m: \mathbb{N}, \exists z: \mathbb{Z}, \operatorname{PowerSeries.coeff}\left(m, \operatorname{A}\right) = (z: \mathbb{Q})$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/HannaA181074Integrality.result` (`✓ std3`). ∎

*Resolves.* `Problems/hanna181074` (proved) by `D5/S1/Recurrence/Algebraic/HannaA181074Integrality.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hanna181074","declaration_gid":"D5/S1/Recurrence/Algebraic/HannaA181074Integrality.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2010). *OEIS A181070, A181074, A181078 and A181080 integrality conjectures*. URL: <https://oeis.org/A181070>.

*Commentary.*

Every coefficient of the displayed formal exponential is an integer. The prime-scaling congruence and diagonal identity reduce the assertion to the Dold exponential integrality criterion.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA181074Integrality.A`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA181074Integrality.claim`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA181074Integrality.logarithm`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA181074Integrality.negbinomCong`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA181074Integrality.negbinomDiv`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA181074Integrality.result`
- Dependency: [D5/S1/Recurrence/Algebraic/HannaA181070Integrality](HannaA181070Integrality.md)
