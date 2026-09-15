# Ordowski's Binomial and Power-Sum Least Prime

## Abstract

Ordowski's binomial and power-sum conditions define the same least prime in OEIS A133907.

All variables and values lie in the natural numbers N, including zero. Here n is the index, p and q are candidate primes, and k is the summation index. Prime(p) means that p is prime, C(u,v) is the natural binomial coefficient, and a is A133907 as defined below. The operator sInf takes the infimum in N, equal to the least element of a nonempty set and zero for the empty set. The sum runs over all natural k from 1 through n, inclusive; powers and the truncated subtraction p-1 are natural-number operations. Congruence modulo p means equality of residues, and the order is the natural-number order. For every prime p, both membership conditions are equivalent to p dividing floor(n/p): Lucas gives the binomial residue, and Fermat together with the count of multiples gives the power-sum residue. Here n/p is natural-number division, namely floor(n/p). Only the Conjecture sentence of Ordowski's comment is settled; the clause 'Thus a(n) >= A317358(n)' is a consequence, not claimed separately.

**Definition 1.1 (The A133907 sequence).**

$$\forall n \in \mathbb{N},\; \operatorname{a}\left(n\right) = \operatorname{sInf}\left(\{p \in \mathbb{N} \mid (\operatorname{Prime}\left(p\right)) \land (\operatorname{C}\left(n + p, p\right) \equiv 1 (\operatorname{mod} p))\}\right)$$

*Formalization.* `D5/S3/Arith/Congruence/OrdowskiBinomialPowerSumLeastPrime.a` (`✓ std3`).

*Citation.* Thomas Ordowski (2018). *OEIS A133907, least prime p with binomial(n+p,p) ≡ 1 (mod p), with the power-sum least-prime conjecture*. URL: <https://oeis.org/A133907>.

*Commentary.*

This is the original NAME definition: the least prime p with C(n+p,p) congruent to one modulo p. A prime greater than n satisfies the condition, so the defining set is nonempty and its natural infimum is attained. The OEIS offset is 1,1; the total Lean definition also exists at zero.

**Theorem 1.2 (Ordowski's least-prime conjecture).**

$$\forall n \in \mathbb{N},\; (0 < n) \implies ((\operatorname{a}\left(n\right) \in \{p \in \mathbb{N} \mid (\operatorname{Prime}\left(p\right)) \land ((\sum_{k = 1}^{n} k^{p - 1}) \equiv n (\operatorname{mod} p))\}) \land (\forall q \in \{p \in \mathbb{N} \mid (\operatorname{Prime}\left(p\right)) \land ((\sum_{k = 1}^{n} k^{p - 1}) \equiv n (\operatorname{mod} p))\},\; \operatorname{a}\left(n\right) \leq q))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/OrdowskiBinomialPowerSumLeastPrime.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a133907-ordowski-binomial-power-sum-least-prime` (proved) by `D5/S3/Arith/Congruence/OrdowskiBinomialPowerSumLeastPrime.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a133907-ordowski-binomial-power-sum-least-prime","declaration_gid":"D5/S3/Arith/Congruence/OrdowskiBinomialPowerSumLeastPrime.result","resolution_kind":"proved"} -->

*Citation.* Thomas Ordowski (2018). *OEIS A133907, least prime p with binomial(n+p,p) ≡ 1 (mod p), with the power-sum least-prime conjecture*. URL: <https://oeis.org/A133907>.

*Commentary.*

For every n > 0, a(n) belongs to the displayed power-sum prime set and is at most every element q of that set. This membership-and-minimality conjunction renders Lean's IsLeast without dropping either obligation. For a prime p, Lucas gives C(n+p,p) congruent to floor(n/p)+1. Fermat gives the sum congruent to n-floor(n/p), with subtraction interpreted in the residue field ZMod p. Both conditions reduce to p dividing floor(n/p), and the natural infimum transfers across their pointwise equivalence. All auxiliary facts are local steps inside result; the positive-index hypothesis is retained. The unsigned floor-division comment is explanatory and receives no separate resolution claim.

## References

- Truth anchor: `D5/S3/Arith/Congruence/OrdowskiBinomialPowerSumLeastPrime.a`
- Truth anchor: `D5/S3/Arith/Congruence/OrdowskiBinomialPowerSumLeastPrime.result`
