# Component Consequences of Lehmer's Totient Condition

## Abstract

Six general arithmetic consequences of Lehmer's totient divisibility condition.

**Theorem 1.1 (A repeated prime factor enters the totient).**

$$\forall p \in \mathbb{N},\; \forall n \in \mathbb{N},\; \left(Prime\left(p\right) \land p^{2} \mid n\right) \Rightarrow p \mid phi\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/LehmerTotientDichotomy.prime_dvd_totient_of_prime_sq_dvd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If p is prime and p squared divides n, then p divides Euler's totient of n.

**Theorem 1.2 (The Lehmer condition forces squarefreeness).**

$$\forall n \in \mathbb{N},\; \left(1 < n \land phi\left(n\right) \mid n - 1\right) \Rightarrow Squarefree\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/LehmerTotientDichotomy.squarefree_of_totient_dvd_sub_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n greater than one, totient divisibility by n minus one rules out every repeated prime factor.

**Theorem 1.3 (The squarefree totient product formula).**

$$\forall n \in \mathbb{N},\; \left(n \ne 0 \land Squarefree\left(n\right)\right) \Rightarrow phi\left(n\right) = \prod_{p \in primeFactors\left(n\right)} (p - 1)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/LehmerTotientDichotomy.totient_eq_primeFactors_sub_one_prod` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonzero squarefree n, Euler's totient is the product of p minus one over its distinct prime factors.

**Theorem 1.4 (The composite Lehmer branch is odd).**

$$\forall n \in \mathbb{N},\; \left(\left(1 < n \land phi\left(n\right) \mid n - 1\right) \land \left(\neg Prime\left(n\right)\right)\right) \Rightarrow Odd\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/LehmerTotientDichotomy.odd_of_totient_dvd_sub_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A composite n greater than one whose totient divides n minus one must be odd.

**Theorem 1.5 (The prime-factor count gives a two-adic divisor).**

$$\forall n \in \mathbb{N},\; \left(\left(1 < n \land phi\left(n\right) \mid n - 1\right) \land \left(\neg Prime\left(n\right)\right)\right) \Rightarrow 2^{card\left(primeFactors\left(n\right)\right)} \mid n - 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/LehmerTotientDichotomy.two_pow_primeFactors_card_dvd_sub_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the composite branch, two to the number of distinct prime factors divides n minus one.

**Theorem 1.6 (The composite branch has at least three distinct prime factors).**

$$\forall n \in \mathbb{N},\; \left(\left(1 < n \land phi\left(n\right) \mid n - 1\right) \land \left(\neg Prime\left(n\right)\right)\right) \Rightarrow 3 \le card\left(primeFactors\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/LehmerTotientDichotomy.three_le_primeFactors_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A composite Lehmer candidate cannot have zero, one, or two distinct prime factors.

## References

- Truth anchor: `D5/S3/Factorization/LehmerTotientDichotomy.odd_of_totient_dvd_sub_one`
- Truth anchor: `D5/S3/Factorization/LehmerTotientDichotomy.prime_dvd_totient_of_prime_sq_dvd`
- Truth anchor: `D5/S3/Factorization/LehmerTotientDichotomy.squarefree_of_totient_dvd_sub_one`
- Truth anchor: `D5/S3/Factorization/LehmerTotientDichotomy.three_le_primeFactors_card`
- Truth anchor: `D5/S3/Factorization/LehmerTotientDichotomy.totient_eq_primeFactors_sub_one_prod`
- Truth anchor: `D5/S3/Factorization/LehmerTotientDichotomy.two_pow_primeFactors_card_dvd_sub_one`
