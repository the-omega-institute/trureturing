# Divisor Count and Radical Rigidity

## Abstract

A positive integer whose divisor count divides its squarefree kernel has those two quantities equal.

**Theorem 1.1 (Divisibility forces equality).**

$$\forall k \in \mathbb{N},\ 1 \le k \Rightarrow \operatorname{card}\left(\operatorname{divisors}\left(k\right)\right) \mid \operatorname{radical}\left(k\right) \Rightarrow \operatorname{radical}\left(k\right) = \operatorname{card}\left(\operatorname{divisors}\left(k\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/DivisorCountRadicalCoincidence.radical_eq_card_divisors_of_dvd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The radical is squarefree, so every divisor of it is squarefree. The prime-exponent product for the divisor count contributes at least one prime factor for every distinct prime factor of k. Divisibility gives the reverse bound on distinct prime factors. The two prime-factor sets therefore coincide, and their products give the stated equality.

## References

- Truth anchor: `D5/S3/Arith/DivisorCountRadicalCoincidence.radical_eq_card_divisors_of_dvd`
