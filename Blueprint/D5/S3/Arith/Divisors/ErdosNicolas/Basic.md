# Reciprocal divisor differences and the original claim

## Abstract

Reciprocal divisor differences and the original claim

**Definition 1.1 (Unordered reciprocal gaps).**

$$\forall S \in \operatorname{Finset}\left(\mathbb{N}\right),\; \operatorname{pairSum}\left(S\right) = \sum_{d \in S} (\sum_{e \in S} (\operatorname{ite}\left(d < e, \frac{1}{e - d}, 0\right)))$$

*Formalization.* `D5/S3/Arith/Divisors/ErdosNicolas/Basic.pairSum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* P. Erdős and J.-L. Nicolas (1989). *On functions connected with prime divisors of an integer*. URL: <https://oeis.org/A330076>.

*Commentary.*

Each unordered pair of distinct natural points is counted once. Subtraction is natural subtraction, and reciprocals and sums lie in the rationals. The conditional excludes all zero gaps.

**Definition 1.2 (The divisor difference sum).**

$$\forall n \in \mathbb{N},\; \operatorname{Hhat}\left(n\right) = \operatorname{pairSum}\left(\operatorname{divisors}\left(n\right)\right)$$

*Formalization.* `D5/S3/Arith/Divisors/ErdosNicolas/Basic.hHat` (`✓ std3`).

*Citation.* P. Erdős and J.-L. Nicolas (1989). *On functions connected with prime divisors of an integer*. URL: <https://oeis.org/A330076>.

*Commentary.*

On p. 390 of the cited source, the positive divisors are ordered d₁<⋯<dτ(n), and Ĥ(n) is the sum of 1/(dⱼ−dᵢ) over i<j. Nat.divisors gives the same finite set for positive n. Its value at zero is the empty set, outside the conjecture's range.

**Theorem 1.3 (The prime-power bound).**

$$\forall p \in \mathbb{N},\; \forall a \in \mathbb{N},\; \operatorname{Prime}\left(p\right) \Rightarrow \operatorname{Hhat}\left(p^{a}\right) \le a$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/ErdosNicolas/Basic.hHat_prime_pow_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* P. Erdős and J.-L. Nicolas (1989). *On functions connected with prime divisors of an integer*. URL: <https://oeis.org/A330076>.

*Commentary.*

Each positive-exponent row contributes at most one, so the reciprocal gap sum is at most the exponent. This is one less than the number of divisors of the prime power.

**Definition 1.4 (The published conjecture).**

$$ErdosNicolasClaim = \left(\forall n \in \mathbb{N},\; 5040 < n \Rightarrow \operatorname{Hhat}\left(n\right) < \operatorname{card}\left(\operatorname{divisors}\left(n\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/Divisors/ErdosNicolas/Basic.ErdosNicolasClaim` (`✓ std3`).

*Citation.* P. Erdős and J.-L. Nicolas (1989). *On functions connected with prime divisors of an integer*. URL: <https://oeis.org/A330076>.

*Commentary.*

Page 390, verbatim: “We conjecture that for n > 5040, we have Ĥ(n) < τ(n).” The quantifier is over every natural n above 5040, with no restriction on its prime exponents or divisor count.

## References

- Truth anchor: `D5/S3/Arith/Divisors/ErdosNicolas/Basic.ErdosNicolasClaim`
- Truth anchor: `D5/S3/Arith/Divisors/ErdosNicolas/Basic.hHat`
- Truth anchor: `D5/S3/Arith/Divisors/ErdosNicolas/Basic.hHat_prime_pow_le`
- Truth anchor: `D5/S3/Arith/Divisors/ErdosNicolas/Basic.pairSum`
