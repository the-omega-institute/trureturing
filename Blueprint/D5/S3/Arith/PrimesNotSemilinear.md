# One Together with the Primes Is Not Semilinear

## Abstract

The natural primes together with one form a set that is not semilinear.

**Theorem 1.1 (Nonsemilinearity of the prime set with one adjoined).**

$$\neg IsSemilinearSet\left(\{1\}\cup\mathbb{P}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/PrimesNotSemilinear.primes_union_one_not_isSemilinearSet` (`✓ std3`). ∎

*Citation.* Gilles (2012). *Prove that the language of non-prime numbers written in unary is not regular*. URL: <https://cs.stackexchange.com/a/4986>.

*Commentary.*

Here P denotes the set of prime natural numbers, and the ambient set is N. A semilinear subset of N has a positive period d beyond some threshold k.

Choose a prime p greater than both k and d. Repeated translation by d keeps p + m*d in the set for every natural m. With m = p, this gives p + p*d = p*(1+d). Both factors exceed one, so this number is composite and exceeds one. It cannot belong to the set, contradicting periodicity.

## References

- Truth anchor: `D5/S3/Arith/PrimesNotSemilinear.primes_union_one_not_isSemilinearSet`
