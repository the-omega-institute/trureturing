# Prime Divisor-Pair Sums and Their Preimages

## Abstract

Prime values of the second elementary symmetric divisor function have exactly two preimages when attained at composites.

All variables range over the natural numbers. The function S2 sums the products of unordered pairs of distinct positive divisors.

**Definition 1.1 (The second elementary symmetric divisor function).**

$$\forall n \in \mathbb{N}, \left(S_{2}\right)\left(n\right) = \sum_{d \mid n, e \mid n, d < e} d \cdot e$$

*Formalization.* `D5/S1/Recurrence/Invariants/DivisorPairProductPrimePreimages.S2` (`✓ std3`).

*Citation.* Zak Seidov (2006). *OEIS A119623, Composite numbers for which the second elementary symmetric function of divisors is prime*. URL: <https://oeis.org/A119623>.

*Commentary.*

For each n, S2(n) is the sum of d times e over positive divisors d and e of n with d less than e.

**Theorem 1.2 (Classification of composite prime-value arguments).**

$$\begin{aligned}\forall n \in \mathbb{N},\\\neg \operatorname{Prime}(n) \implies 1 < n \implies \operatorname{Prime}(\left(S_{2}\right)\left(n\right)) \implies \\\exists q \in \mathbb{N}, \operatorname{Prime}(q) \land \operatorname{Odd}(q) \land n = 2 \cdot q\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/DivisorPairProductPrimePreimages.eq_two_mul_prime_of_composite_of_s2_prime` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The divisor-sum identity separates repeated prime factors from squarefree arguments. A repeated prime factor produces a common factor of the first and second power sums, while parity excludes squarefree arguments with at least two odd prime factors. The remaining composite is twice an odd prime.

**Theorem 1.3 (Seidov's exact two-preimage conjecture).**

$$\begin{aligned}\forall n \in \mathbb{N},\\\neg \operatorname{Prime}(n) \implies 1 < n \implies \operatorname{Prime}(\left(S_{2}\right)\left(n\right)) \implies \\\forall m \in \mathbb{N}, \left(S_{2}\right)\left(m\right) = \left(S_{2}\right)\left(n\right) \iff (m = n \lor m = \left(S_{2}\right)\left(n\right))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/DivisorPairProductPrimePreimages.seidov_conjecture` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a119623-divisor-pair-product-prime-preimages` (proved) by `D5/S1/Recurrence/Invariants/DivisorPairProductPrimePreimages.seidov_conjecture`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a119623-divisor-pair-product-prime-preimages","declaration_gid":"D5/S1/Recurrence/Invariants/DivisorPairProductPrimePreimages.seidov_conjecture","resolution_kind":"proved"} -->

*Citation.* Zak Seidov (2006). *OEIS A119623, Composite numbers for which the second elementary symmetric function of divisors is prime*. URL: <https://oeis.org/A119623>.

*Commentary.*

For a composite n whose S2 value is prime, the equality S2(m)=S2(n) holds exactly when m is n or the prime S2(n). The classification above reduces composite arguments to twice an odd prime. The evaluations S2(p)=p and S2(2q)=2q^2+9q+2, together with strict increase of the latter expression, separate all remaining cases, including m equal to zero or one.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/DivisorPairProductPrimePreimages.S2`
- Truth anchor: `D5/S1/Recurrence/Invariants/DivisorPairProductPrimePreimages.eq_two_mul_prime_of_composite_of_s2_prime`
- Truth anchor: `D5/S1/Recurrence/Invariants/DivisorPairProductPrimePreimages.seidov_conjecture`
