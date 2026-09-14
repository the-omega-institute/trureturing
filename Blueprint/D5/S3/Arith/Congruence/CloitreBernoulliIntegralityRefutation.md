# The OEIS A090825 Bernoulli-Integrality Conjecture

## Abstract

The integer 833 refutes Cloitre's Bernoulli-integrality conjecture for A090825.

**Definition 1.1 (The rational expression defining A090825).**

$$\forall n \in \mathrm{Nat},\; \operatorname{F}\left(n\right) = \frac{3}{2} \cdot \frac{1}{n} \cdot \left(2 \cdot n + 1\right) \cdot \left(3^{n} + 1\right) \cdot \operatorname{B}\left(2 \cdot n\right)$$

*Formalization.* `D5/S3/Arith/Congruence/CloitreBernoulliIntegralityRefutation.F` (`✓ std3`).

*Citation.* Benoit Cloitre (2004). *OEIS A090825, nonprimes n such that (3/2)(1/n)(2n+1)(3^n+1)B(2n) is an integer*. URL: <https://oeis.org/A090825>.

*Commentary.*

Every factor is multiplied in the rationals. Here B(2n) is the Bernoulli number with even index 2n, while 3/2 and 1/n are rational quotients.

**Definition 1.2 (The prime sequence A053176).**

$$\forall p \in \mathrm{Nat},\; (\operatorname{A053176}\left(p\right)) \Leftrightarrow ((\operatorname{Prime}\left(p\right)) \land (\neg \operatorname{Prime}\left(2 \cdot p + 1\right)))$$

*Formalization.* `D5/S3/Arith/Congruence/CloitreBernoulliIntegralityRefutation.A053176` (`✓ std3`).

*Citation.* Benoit Cloitre (2004). *OEIS A090825, nonprimes n such that (3/2)(1/n)(2n+1)(3^n+1)B(2n) is an integer*. URL: <https://oeis.org/A090825>.

*Commentary.*

A natural p lies in A053176 exactly when p is prime and 2p+1 is not prime.

**Definition 1.3 (Cloitre's composite-factor integrality conjecture).**

$$(claim) \Leftrightarrow (\forall n \in \mathrm{Nat},\; (1 < n) \Rightarrow ((\neg \operatorname{Prime}\left(n\right)) \Rightarrow ((\forall p \in \mathrm{Nat},\; (\operatorname{Prime}\left(p\right)) \Rightarrow ((p \mid n) \Rightarrow (\operatorname{A053176}\left(p\right)))) \Rightarrow (\exists z \in \mathbb{Z},\; \operatorname{F}\left(n\right) = (z : \mathbb{Q})))))$$

*Formalization.* `D5/S3/Arith/Congruence/CloitreBernoulliIntegralityRefutation.claim` (`✓ std3`).

*Citation.* Benoit Cloitre (2004). *OEIS A090825, nonprimes n such that (3/2)(1/n)(2n+1)(3^n+1)B(2n) is an integer*. URL: <https://oeis.org/A090825>.

*Commentary.*

For every composite natural n greater than one, the conjecture asserts that F(n) is an integer whenever each prime divisor of n belongs to A053176.

**Theorem 1.4 (The conjecture fails at n = 833).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/CloitreBernoulliIntegralityRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a090825-bernoulli-integrality-refutation` (refuted) by `D5/S3/Arith/Congruence/CloitreBernoulliIntegralityRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a090825-bernoulli-integrality-refutation","declaration_gid":"D5/S3/Arith/Congruence/CloitreBernoulliIntegralityRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Benoit Cloitre (2004). *OEIS A090825, nonprimes n such that (3/2)(1/n)(2n+1)(3^n+1)B(2n) is an integer*. URL: <https://oeis.org/A090825>.

*Commentary.*

The integer 833 has prime factors 7 and 17, both in A053176. The von Staudt-Clausen theorem gives the Bernoulli factor valuation minus one at 239, while every other factor has valuation zero. Thus F(833) is not an integer. The separate prime congruence clause and the subsequence question are untouched.

## References

- Truth anchor: `D5/S3/Arith/Congruence/CloitreBernoulliIntegralityRefutation.A053176`
- Truth anchor: `D5/S3/Arith/Congruence/CloitreBernoulliIntegralityRefutation.F`
- Truth anchor: `D5/S3/Arith/Congruence/CloitreBernoulliIntegralityRefutation.claim`
- Truth anchor: `D5/S3/Arith/Congruence/CloitreBernoulliIntegralityRefutation.result`
