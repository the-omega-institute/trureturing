# Squares Preserved by a Decimal Prefix and Suffix

## Abstract

Wu's A249621 conjecture for squares preserved by a decimal prefix and suffix.

For a natural number x, the base-ten digits are written by Nat.digits 10 x. Prepending 1 and appending 25 produces the value 10^(length(digits(10,x)) + 2) + 100*x + 25.

**Definition 1.1 (A249621 membership).**

$$\forall x \in Nat,\; \operatorname{IsMember}\left(x\right) \Leftrightarrow (\left(\exists z \in Nat,\; x = z^{2}\right) \land \left(\exists y \in Nat,\; y^{2} = 10^{\operatorname{length}\left(\operatorname{digits}\left(10, x\right)\right) + 2} + 100 \cdot x + 25\right))$$

*Formalization.* `D5/S1/Digit/Admissibility/SquarePrependOneAppendTwentyFive.IsMember` (`✓ std3`).

*Citation.* Chai Wah Wu (2014). *OEIS A249621, Squares that remain squares when prepended with 1 and appended with 25 in base 10*. URL: <https://oeis.org/A249621>.

*Commentary.*

Membership requires x to be a square and the base-ten concatenation 1||x||25 to be a square as well.

**Theorem 1.2 (Wu's terminal-digit conjecture).**

$$\forall x \in Nat,\; x > 0 \Rightarrow \left(\operatorname{IsMember}\left(x\right) \Rightarrow \left(x \bmod 100 = 0 \lor x \bmod 100 = 56\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Admissibility/SquarePrependOneAppendTwentyFive.wu_a249621` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a249621-square-prepend-one-append-twenty-five` (proved) by `D5/S1/Digit/Admissibility/SquarePrependOneAppendTwentyFive.wu_a249621`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a249621-square-prepend-one-append-twenty-five","declaration_gid":"D5/S1/Digit/Admissibility/SquarePrependOneAppendTwentyFive.wu_a249621","resolution_kind":"proved"} -->

*Citation.* Chai Wah Wu (2014). *OEIS A249621, Squares that remain squares when prepended with 1 and appended with 25 in base 10*. URL: <https://oeis.org/A249621>.

*Commentary.*

Every member x with x at least 1 has final two decimal digits 00 or 56. The proof reduces the second square root modulo 5, then classifies the resulting square congruence modulo 400.

## References

- Truth anchor: `D5/S1/Digit/Admissibility/SquarePrependOneAppendTwentyFive.IsMember`
- Truth anchor: `D5/S1/Digit/Admissibility/SquarePrependOneAppendTwentyFive.wu_a249621`
