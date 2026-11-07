# Wu's A227244 Conjecture 2

## Abstract

The least prime divisor on this entire arithmetic progression is 47.

**Theorem 1.1 (The full equality for every natural index).**

$$\forall n \in \mathbb{N},\; (\operatorname{Prime}\left(47\right)) \land (((47: \mathbb{Z}) \mid (((2: \mathbb{Z})^{2^{220*n+8}}+1)*(2: \mathbb{Z})^{2^{2^{220*n+8}}}-1)) \land (\forall q \in \mathbb{N},\; (\operatorname{Prime}\left(q\right)) \Rightarrow (((q: \mathbb{Z}) \mid (((2: \mathbb{Z})^{2^{220*n+8}}+1)*(2: \mathbb{Z})^{2^{2^{220*n+8}}}-1)) \Rightarrow (47 \le q))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/WuA227244C2Equality.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a227244-c2-equality` (proved) by `D5/S3/Arith/Congruence/WuA227244C2Equality.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a227244-c2-equality","declaration_gid":"D5/S3/Arith/Congruence/WuA227244C2Equality.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Chai Wah Wu (2026). *OEIS A227244, least prime factors of an iterated binary power product*. URL: <https://oeis.org/A227244/internal>.

*Commentary.*

For every natural n, including zero, the integer with index 220*n+8 is divisible by the prime 47, and every natural prime divisor is at least 47. The product and subtraction are in the integers and every exponent is natural. Periodicity reduces the modular powers to finite residue tables; the reduction identities apply at every natural index. The tables prove divisibility by 47 and exclude each smaller prime. Thus the finite certificates establish the entire unbounded equality, without an exclusion or an upper bound on n.

## References

- Truth anchor: `D5/S3/Arith/Congruence/WuA227244C2Equality.result`
- Dependency: [D5/S3/Arith/Primes/WuA227244ConjectureFour](../Primes/WuA227244ConjectureFour.md)
