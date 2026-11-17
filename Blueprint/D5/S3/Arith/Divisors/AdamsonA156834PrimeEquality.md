# Adamson's OEIS A156834 prime-equality conjecture

## Abstract

Adamson's A156834 equals its index exactly at primes greater than one.

**Definition 1.1 (The totient-weighted divisor sum).**

$$\forall n \in \mathrm{Nat},\; a\left(n\right) = \sum_{d \in \operatorname{Nat}.\operatorname{divisors}\left(n\right)} (\operatorname{Nat}.\operatorname{totient}\left(d\right) \cdot \operatorname{Nat}.\operatorname{choose}\left(d + \operatorname{Nat}.\operatorname{div}\left(n, d\right) - 2, d - 1\right))$$

*Formalization.* `D5/S3/Arith/Divisors/AdamsonA156834PrimeEquality.a` (`✓ std3`).

*Citation.* el Houcein el Abdalaoui; Mohamed Dahmoune; Djelloul Ziadi (2013). *On the transition reduction problem for finite automata*. DOI: [10.48550/arXiv.1301.3751](https://doi.org/10.48550/arXiv.1301.3751). URL: <https://arxiv.org/abs/1301.3751v1>.

*Commentary.*

OEIS A156834, FORMULA (revision 20, unpaginated), states: "a(n) = Sum_{d|n} phi(d) * binomial(d+n/d-2, d-1)." The formula is due to Seiichi Manyama. Here n and d are natural numbers; Nat.divisors n contains the positive divisors, Nat.totient is Euler's totient with Nat.totient 1 = 1, and Nat.choose is the ordinary binomial coefficient. Nat.div is natural-number integer division and subtraction in this formula is natural subtraction. For a positive divisor d, both d and n / d are positive. The binomial factor is the entry in row n and column d of the Eratosthenes-Pascal triangle in el Abdalaoui–Dahmoune–Ziadi, arXiv:1301.3751v1, §5.2, Proposition 6, p. 11. The sequence starts at n = 1; the total function's value at zero is outside the assertion.

**Definition 1.2 (Adamson's prime-equality assertion).**

$$claim = (\forall n \in \mathrm{Nat},\; (1 < n) \Rightarrow ((a\left(n\right) = n) \Leftrightarrow (\operatorname{Nat}.\operatorname{Prime}\left(n\right))))$$

*Formalization.* `D5/S3/Arith/Divisors/AdamsonA156834PrimeEquality.claim` (`✓ std3`).

*Citation.* el Houcein el Abdalaoui; Mohamed Dahmoune; Djelloul Ziadi (2013). *On the transition reduction problem for finite automata*. DOI: [10.48550/arXiv.1301.3751](https://doi.org/10.48550/arXiv.1301.3751). URL: <https://arxiv.org/abs/1301.3751v1>.

*Commentary.*

OEIS A156834, COMMENTS (revision 20, unpaginated), states verbatim: "Conjecture: for n>1, a(n) = n iff n is prime. Companion to A156833." The variable n ranges over Nat, the antecedent is 1 < n, and primality is Nat.Prime n. Both directions of the equivalence are asserted.

**Theorem 1.3 (Equality characterizes prime indices).**

$$\forall n \in \mathrm{Nat},\; (1 < n) \Rightarrow ((a\left(n\right) = n) \Leftrightarrow (\operatorname{Nat}.\operatorname{Prime}\left(n\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/AdamsonA156834PrimeEquality.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* el Houcein el Abdalaoui; Mohamed Dahmoune; Djelloul Ziadi (2013). *On the transition reduction problem for finite automata*. DOI: [10.48550/arXiv.1301.3751](https://doi.org/10.48550/arXiv.1301.3751). URL: <https://arxiv.org/abs/1301.3751v1>.

*Commentary.*

Subtracting Nat.sum_totient from the defining sum expresses the integer difference a n − n as a sum of products of Nat.totient d with the binomial coefficient's excess over one. Nat.choose_pos and Nat.choose_eq_one_iff show that these terms are nonnegative, and vanish exactly at the divisor endpoints d = 1 and d = n. For prime n, every divisor is an endpoint. For composite n > 1, a proper divisor has a strictly positive contribution, so n < a n. Thus the weighted sequence has the claimed equality precisely at prime indices. The companion A156833 assertion is a separate question.

## References

- Truth anchor: `D5/S3/Arith/Divisors/AdamsonA156834PrimeEquality.a`
- Truth anchor: `D5/S3/Arith/Divisors/AdamsonA156834PrimeEquality.claim`
- Truth anchor: `D5/S3/Arith/Divisors/AdamsonA156834PrimeEquality.result`
