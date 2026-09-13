# Least Numbers with a Prescribed Even-Divisor Count

## Abstract

The positive-index form of Gerasimov's A187941 conjecture. The literal offset-0 reading of the comment fails at n = 0, since a(0) = 1 = 2^0 while 0 is neither prime nor 1; this endpoint is disclosed here and not formalized.

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

**Theorem 1.3 (The positive-index implication).**

$$\forall n \in \mathrm{Nat},\; 1 \le n \Rightarrow \left(\operatorname{a}\left(n\right) = 2^{n} \Rightarrow \left((\operatorname{Prime}\left(n\right)) \lor (n = 1)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/GerasimovLeastEvenDivisorCountPowerOfTwo.gerasimov_a187941` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Juri-Stepan Gerasimov (2011). *OEIS A187941, Least number with exactly n even divisors*. URL: <https://oeis.org/A187941>.

*Commentary.*

For composite n = d times e, the multiplicative count E(2^d times 3^(e-1)) = d times e gives a smaller witness than 2^n. Thus equality with 2^n at a positive index forces n to be prime or one.

## References

- Truth anchor: `D5/S3/Factorization/GerasimovLeastEvenDivisorCountPowerOfTwo.E`
- Truth anchor: `D5/S3/Factorization/GerasimovLeastEvenDivisorCountPowerOfTwo.a`
- Truth anchor: `D5/S3/Factorization/GerasimovLeastEvenDivisorCountPowerOfTwo.gerasimov_a187941`
