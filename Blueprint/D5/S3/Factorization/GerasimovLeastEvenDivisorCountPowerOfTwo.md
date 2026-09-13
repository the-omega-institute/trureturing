# Least Numbers with a Prescribed Even-Divisor Count

## Abstract

The literal offset-zero form of Gerasimov's A187941 conjecture and its positive-index form.

**Definition 1.1 (Even-divisor count).**

$$\forall m \in \mathrm{Nat},\; \operatorname{E}\left(m\right) = \operatorname{card}\left(\operatorname{filter}\left(Even, \operatorname{divisors}\left(m\right)\right)\right)$$

*Formalization.* `D5/S3/Factorization/GerasimovLeastEvenDivisorCountPowerOfTwo.E` (`✓ std3`).

*Citation.* Juri-Stepan Gerasimov (2011). *OEIS A187941, Least number with exactly n even divisors*. URL: <https://oeis.org/A187941>.

*Commentary.*

E(m) is the cardinality of the even members of the natural divisor finset of m.

**Definition 1.2 (Least number with n even divisors).**

$$\forall n \in \mathrm{Nat},\; \operatorname{a}\left(n\right) = \operatorname{sInf}\left(\{m \in \mathrm{Nat} \mid (0 < m) \land (\operatorname{E}\left(m\right) = n)\}\right)$$

*Formalization.* `D5/S3/Factorization/GerasimovLeastEvenDivisorCountPowerOfTwo.a` (`✓ std3`).

*Citation.* Juri-Stepan Gerasimov (2011). *OEIS A187941, Least number with exactly n even divisors*. URL: <https://oeis.org/A187941>.

*Commentary.*

The natural infimum selects the least positive number with the prescribed even-divisor count. The set is nonempty for every n; by convention, sInf of the empty set is zero.

**Definition 1.3 (The literal offset-zero conjecture).**

$$(claim) \Leftrightarrow (\forall n \in \mathrm{Nat},\; \operatorname{a}\left(n\right) = 2^{n} \Rightarrow \left((\operatorname{Prime}\left(n\right)) \lor (n = 1)\right))$$

*Formalization.* `D5/S3/Factorization/GerasimovLeastEvenDivisorCountPowerOfTwo.claim` (`✓ std3`).

*Citation.* Juri-Stepan Gerasimov (2011). *OEIS A187941, Least number with exactly n even divisors*. URL: <https://oeis.org/A187941>.

*Commentary.*

The entry has offset zero, so this literal universal statement includes n = 0.

**Theorem 1.4 (The offset-zero conjecture is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/GerasimovLeastEvenDivisorCountPowerOfTwo.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Juri-Stepan Gerasimov (2011). *OEIS A187941, Least number with exactly n even divisors*. URL: <https://oeis.org/A187941>.

*Commentary.*

At n = 0, the least number with no even divisors is a(0) = 1 = 2^0, while zero is neither prime nor equal to one.

**Theorem 1.5 (The positive-index implication).**

$$\forall n \in \mathrm{Nat},\; 1 \le n \Rightarrow \left(\operatorname{a}\left(n\right) = 2^{n} \Rightarrow \left((\operatorname{Prime}\left(n\right)) \lor (n = 1)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/GerasimovLeastEvenDivisorCountPowerOfTwo.gerasimov_a187941` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Juri-Stepan Gerasimov (2011). *OEIS A187941, Least number with exactly n even divisors*. URL: <https://oeis.org/A187941>.

*Commentary.*

For composite n = d times e, the multiplicative count E(2^d times 3^(e-1)) = d times e gives a smaller witness than 2^n. Thus equality with 2^n at a positive index forces n to be prime or one.

## References

- Truth anchor: `D5/S3/Factorization/GerasimovLeastEvenDivisorCountPowerOfTwo.E`
- Truth anchor: `D5/S3/Factorization/GerasimovLeastEvenDivisorCountPowerOfTwo.a`
- Truth anchor: `D5/S3/Factorization/GerasimovLeastEvenDivisorCountPowerOfTwo.claim`
- Truth anchor: `D5/S3/Factorization/GerasimovLeastEvenDivisorCountPowerOfTwo.gerasimov_a187941`
- Truth anchor: `D5/S3/Factorization/GerasimovLeastEvenDivisorCountPowerOfTwo.result`
