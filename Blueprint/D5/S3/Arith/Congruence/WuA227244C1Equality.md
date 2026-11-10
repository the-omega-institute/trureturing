# Wu's A227244 Conjecture 1

## Abstract

The least prime divisor on this entire arithmetic progression is 101.

**Theorem 1.1 (The full equality for every natural index).**

$$\forall n \in \mathbb{N},\; (\operatorname{Prime}\left(101\right)) \land (((101: \mathbb{Z}) \mid (((2: \mathbb{Z})^{2^{20*n+16}}+1)*(2: \mathbb{Z})^{2^{2^{20*n+16}}}-1)) \land (\forall q \in \mathbb{N},\; (\operatorname{Prime}\left(q\right)) \Rightarrow (((q: \mathbb{Z}) \mid (((2: \mathbb{Z})^{2^{20*n+16}}+1)*(2: \mathbb{Z})^{2^{2^{20*n+16}}}-1)) \Rightarrow (101 \le q))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/WuA227244C1Equality.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a227244-c1-equality` (proved) by `D5/S3/Arith/Congruence/WuA227244C1Equality.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a227244-c1-equality","declaration_gid":"D5/S3/Arith/Congruence/WuA227244C1Equality.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Chai Wah Wu (2026). *OEIS A227244, least prime factors of an iterated binary power product*. URL: <https://oeis.org/A227244/internal>.

*Commentary.*

For every natural n, including zero, the integer with index 20*n+16 is divisible by the prime 101, and every natural prime divisor is at least 101. The product and subtraction are in the integers and every exponent is natural. Periodicity reduces the modular powers to finite residue tables; the reduction identities apply at every natural index. The tables prove divisibility by 101 and exclude each smaller prime. Thus the finite certificates establish the entire unbounded equality, without an exclusion or an upper bound on n.

## References

- Truth anchor: `D5/S3/Arith/Congruence/WuA227244C1Equality.result`
- Dependency: [D5/S3/Arith/Primes/WuA227244ConjectureFour](../Primes/WuA227244ConjectureFour.md)
