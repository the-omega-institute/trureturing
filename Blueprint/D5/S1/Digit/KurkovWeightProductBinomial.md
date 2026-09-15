# Kurkov's Binary-Weight Product Identity

## Abstract

Binary-weight products satisfy Kurkov's binomial identity at every natural index.

The variables m, n, and k range over the natural numbers N, including zero. The functions wt and a take natural values: wt is the frozen binary-weight definition of D5/S1/Digit/DyadicRowPolynomialRecurrence (A000120), reused by import, and a is A284005. The operator div is natural floor division, and binom(r,k) is Nat.choose r k. All additions, products, powers, and sums are in N. Only Kurkov's April 24, 2023 binomial conjecture is asserted here. The 2019 bit-flip recursion, the 2023 mod-2 binomial transform of A329369, and the representation A000005(A283477(n)) are outside this statement.

**Definition 1.1 (The binary-weight product sequence).**

$$(\operatorname{a}\left(0\right) = 1) \land (\forall n \in \mathbb{N}, \operatorname{a}\left(n + 1\right) = (1 + \operatorname{wt}\left(n + 1\right)) \cdot \operatorname{a}\left(\operatorname{div}\left(n + 1, 2\right)\right))$$

*Formalization.* `D5/S1/Digit/KurkovWeightProductBinomial.a` (`✓ std3`).

*Citation.* Antti Karttunen; Mikhail Kurkov (2023). *OEIS A284005, product of (1 + binary weight) over the binary shifts of n, with Kurkov's binomial conjecture*. URL: <https://oeis.org/A284005>.

*Commentary.*

Starting with a(0)=1, each positive index contributes one plus its binary weight before the index is divided by two. The OEIS NAME states the recurrence for indices greater than one; the data supplies a(1)=2, also obtained from the displayed successor clause.

**Theorem 1.2 (Kurkov's binomial identity).**

$$\forall m, n \in \mathbb{N}, \operatorname{a}\left(2^{m} \cdot (2 \cdot n + 1)\right) = \sum_{k = 0}^{m + 1} \operatorname{binom}\left(m + 1, k\right) \cdot \operatorname{a}\left(2^{k} \cdot n\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/KurkovWeightProductBinomial.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a284005-kurkov-weight-product-binomial` (proved) by `D5/S1/Digit/KurkovWeightProductBinomial.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a284005-kurkov-weight-product-binomial","declaration_gid":"D5/S1/Digit/KurkovWeightProductBinomial.result","resolution_kind":"proved"} -->

*Citation.* Antti Karttunen; Mikhail Kurkov (2023). *OEIS A284005, product of (1 + binary weight) over the binary shifts of n, with Kurkov's binomial conjecture*. URL: <https://oeis.org/A284005>.

*Commentary.*

Multiplication by a power of two preserves binary weight. Induction gives a(2^k*n)=(1+wt(n))^k*a(n), including n=0. At odd indices a second induction gives a(2^m*(2*n+1))=(wt(n)+2)^(m+1)*a(n). The binomial expansion of ((1+wt(n))+1)^(m+1), followed by the first identity in each summand, gives the result. The sum includes both endpoints k=0 and k=m+1, exactly Finset.range(m+2).

## References

- Truth anchor: `D5/S1/Digit/KurkovWeightProductBinomial.a`
- Truth anchor: `D5/S1/Digit/KurkovWeightProductBinomial.result`
- Dependency: [D5/S1/Digit/DyadicRowPolynomialRecurrence](DyadicRowPolynomialRecurrence.md)
