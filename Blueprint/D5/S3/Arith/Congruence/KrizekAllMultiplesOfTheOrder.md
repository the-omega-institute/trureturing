# Krizek's A260407 Divisibility at Every Positive Multiple

## Abstract

Krizek's A260407 condition at exponent n-1 is equivalent to the condition at every positive multiple of that exponent.

**Definition 1.1 (The A260407 modulus).**

$$\forall n \in \mathrm{Nat},\; modulus\left(n\right) = (n - 1)^{2} + 1$$

*Formalization.* `D5/S3/Arith/Congruence/KrizekAllMultiplesOfTheOrder.modulus` (`✓ std3`).

*Citation.* M. F. Hasler; Jaroslav Krizek (2016). *OEIS A260407, Numbers n such that (n-1)^2+1 divides 2^(n-1)-1*. URL: <https://oeis.org/A260407>.

*Commentary.*

For each natural n, modulus(n) is (n-1) squared plus one. The subtraction is truncated natural-number subtraction.

**Definition 1.2 (The A260407 membership condition).**

$$\forall n \in \mathrm{Nat},\; (inSequence\left(n\right)) \Leftrightarrow (modulus\left(n\right) \mid 2^{(n - 1)} - 1)$$

*Formalization.* `D5/S3/Arith/Congruence/KrizekAllMultiplesOfTheOrder.inSequence` (`✓ std3`).

*Citation.* M. F. Hasler; Jaroslav Krizek (2016). *OEIS A260407, Numbers n such that (n-1)^2+1 divides 2^(n-1)-1*. URL: <https://oeis.org/A260407>.

*Commentary.*

For each natural n, inSequence(n) holds exactly when modulus(n) divides 2 raised to n-1, minus one. Both subtractions are truncated natural-number subtraction.

**Definition 1.3 (Divisibility at every positive multiple).**

$$\forall n \in \mathrm{Nat},\; (allMultiples\left(n\right)) \Leftrightarrow (\forall k \in \mathrm{Nat},\; (1 \le k) \Rightarrow (modulus\left(n\right) \mid 2^{(k \cdot (n - 1))} - 1))$$

*Formalization.* `D5/S3/Arith/Congruence/KrizekAllMultiplesOfTheOrder.allMultiples` (`✓ std3`).

*Citation.* M. F. Hasler; Jaroslav Krizek (2016). *OEIS A260407, Numbers n such that (n-1)^2+1 divides 2^(n-1)-1*. URL: <https://oeis.org/A260407>.

*Commentary.*

For each natural n, allMultiples(n) holds exactly when every positive natural k gives divisibility at exponent k times n-1.

**Theorem 1.4 (Equivalence of the two conditions).**

$$\forall n \in \mathrm{Nat},\; (1 \le n) \Rightarrow ((inSequence\left(n\right)) \Leftrightarrow (allMultiples\left(n\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/KrizekAllMultiplesOfTheOrder.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a260407-krizek-all-multiples-of-the-order` (proved) by `D5/S3/Arith/Congruence/KrizekAllMultiplesOfTheOrder.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a260407-krizek-all-multiples-of-the-order","declaration_gid":"D5/S3/Arith/Congruence/KrizekAllMultiplesOfTheOrder.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* M. F. Hasler; Jaroslav Krizek (2016). *OEIS A260407, Numbers n such that (n-1)^2+1 divides 2^(n-1)-1*. URL: <https://oeis.org/A260407>.

*Commentary.*

For every natural n at least one, the A260407 membership condition is equivalent to divisibility at every positive multiple of n-1. The forward implication applies the textbook fact that a power minus one divides the corresponding power at a multiple exponent. The converse takes k equal to one. At n equal to one, modulus(n) is one and both divisibility statements hold.

## References

- Truth anchor: `D5/S3/Arith/Congruence/KrizekAllMultiplesOfTheOrder.allMultiples`
- Truth anchor: `D5/S3/Arith/Congruence/KrizekAllMultiplesOfTheOrder.inSequence`
- Truth anchor: `D5/S3/Arith/Congruence/KrizekAllMultiplesOfTheOrder.modulus`
- Truth anchor: `D5/S3/Arith/Congruence/KrizekAllMultiplesOfTheOrder.result`
