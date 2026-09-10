# Structure Forced by Lehmer's Totient Condition

## Abstract

Lehmer's totient divisibility condition forces oddness, squarefreeness, Korselt divisibilities, a two-adic factor, and at least three prime factors unless the number is prime.

**Definition 1.1 (The squarefree Korselt condition).**

$$\forall n \in \mathbb{N},\; IsKorselt\left(n\right) \Leftrightarrow \left(Squarefree\left(n\right) \land \left(\forall p \in \mathbb{N},\; p \in primeFactors\left(n\right) \Rightarrow p - 1 \mid n - 1\right)\right)$$

*Formalization.* `D5/S3/Arith/Congruence/LehmerTotientStructure.IsKorselt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A natural number satisfies IsKorselt when it is squarefree and every prime factor p has p - 1 dividing n - 1. This formulation also applies to primes.

**Theorem 1.2 (The full Lehmer structural alternative).**

$$\forall n \in \mathbb{N},\; \left(1 < n \land phi\left(n\right) \mid n - 1\right) \Rightarrow \left(Prime\left(n\right) \lor \left(\left(\left(\left(\left(Odd\left(n\right) \land Squarefree\left(n\right)\right) \land IsKorselt\left(n\right)\right) \land \prod_{p \in primeFactors\left(n\right)} (p - 1) \mid n - 1\right) \land 2^{card\left(primeFactors\left(n\right)\right)} \mid n - 1\right) \land 3 \le card\left(primeFactors\left(n\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/LehmerTotientStructure.lehmer_totient_structure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If phi(n) divides n - 1 for n greater than one, then n is prime, or n is odd and squarefree, satisfies the Korselt condition, and has all three stated divisibility and prime-factor conclusions. The squarefree step uses the Carmichael function on a hypothetical prime-square divisor. For exactly two distinct odd prime factors p and q, divisibility by (p-1)(q-1) would force it to divide (p-1)+(q-1), which is positive and strictly smaller.

**Theorem 1.3 (The prime-factor predecessor product divides n - 1).**

$$\forall n \in \mathbb{N},\; \left(1 < n \land phi\left(n\right) \mid n - 1\right) \Rightarrow \prod_{p \in primeFactors\left(n\right)} (p - 1) \mid n - 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/LehmerTotientStructure.primeFactors_sub_one_prod_dvd_sub_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same hypotheses, the product of p - 1 over all prime factors divides n - 1. This named consequence follows from the structural alternative; in the prime case the product has the single factor n - 1.

**Theorem 1.4 (Lehmer's condition implies the Korselt condition).**

$$\forall n \in \mathbb{N},\; \left(1 < n \land phi\left(n\right) \mid n - 1\right) \Rightarrow IsKorselt\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/LehmerTotientStructure.isKorselt_of_totient_dvd_sub_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every n greater than one whose totient divides n - 1 satisfies IsKorselt. For a prime this reduces to squarefreeness and the single divisor n - 1; for a composite it is one clause of the structural alternative.

## References

- Truth anchor: `D5/S3/Arith/Congruence/LehmerTotientStructure.IsKorselt`
- Truth anchor: `D5/S3/Arith/Congruence/LehmerTotientStructure.isKorselt_of_totient_dvd_sub_one`
- Truth anchor: `D5/S3/Arith/Congruence/LehmerTotientStructure.lehmer_totient_structure`
- Truth anchor: `D5/S3/Arith/Congruence/LehmerTotientStructure.primeFactors_sub_one_prod_dvd_sub_one`
