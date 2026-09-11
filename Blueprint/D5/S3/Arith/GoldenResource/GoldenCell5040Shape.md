# Prime Exponent Windows From The Residue

## Abstract

The power residue condition pins four prime exponents and leaves a coprime factor.

Suppose the index is divisible by 5040 and the power of three with that index leaves residue 2241. The lower bounds on the exponents of two and three come from the divisibility alone. The upper bounds, and the exponents of five, seven and eighty three, come from five separate small modulus arguments, each of which contradicts the residue.

Indices and exponents are natural numbers. The residue condition is read modulo the index itself. The multiplicative orders used below are of three, in the units modulo 128, 25 and 49 respectively. Note that this does not pin the remaining factor: it says only that the remaining factor shares no prime with two, three, five, seven or eighty three.

**Lemma 1.1 (Four exponents are determined).**

$$\forall n \in \mathbb{N}, 5040 \mid n \land 3^{n} \equiv 2241 (\mathrm{mod} n) \implies 4 \le \operatorname{v}\left(2, n\right) \le 6 \land 2 \le \operatorname{v}\left(3, n\right) \le 3 \land \operatorname{v}\left(5, n\right) = 1 \land \operatorname{v}\left(7, n\right) = 1 \land \operatorname{v}\left(83, n\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/GoldenCell5040Shape.modEq_2241_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Divisibility by 5040 gives the two lower bounds. For the upper bound on two, a seventh power of two in the index would make the index divisible by the order of three modulo 128, forcing residue one there, while 2241 leaves 65. For three, a fourth power would make the power of three vanish modulo 81, while 2241 leaves 54. For five and seven the orders 20 and 42 already divide 5040, so a square of either prime would force residue one against 16 and 36. Finally eighty three divides 2241 but never divides a power of three, so it cannot divide the index.

**Theorem 1.2 (The index has a coprime residual factor).**

$$\forall n \in \mathbb{N}, 5040 \mid n \land 3^{n} \equiv 2241 (\mathrm{mod} n) \implies \exists a, b, r \in \mathbb{N}, n = 2^{a} \cdot 3^{b} \cdot 5 \cdot 7 \cdot r \land 4 \le a \le 6 \land 2 \le b \le 3 \land \operatorname{gcd}\left(r, 17430\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/GoldenCell5040Shape.modEq_2241_shape` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Split the index at the four determined primes. The quotient is a natural number sharing no prime factor with them, nor with eighty three, because each of those exponents was already fixed. The exponent windows carry over unchanged. The residual factor is not claimed to be one: indices with a larger coprime factor also satisfy the residue condition.

## References

- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenCell5040Shape.modEq_2241_factorization`
- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenCell5040Shape.modEq_2241_shape`
