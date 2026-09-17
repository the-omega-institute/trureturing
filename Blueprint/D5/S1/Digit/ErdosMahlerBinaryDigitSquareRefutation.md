# Mahler's Reported Binary-Digit Square Uniqueness

## Abstract

A coprime base-12 square contradicts the reported uniqueness of Mahler's nontrivial binary-digit example.

**Definition 1.1 (Binary-digit squares).**

$$\forall k \in \mathbb{N}, x \in \mathbb{N}, S \in \operatorname{Finset}\left(\mathbb{N}\right),\; (\operatorname{BinaryBaseSquare}\left(k, x, S\right)) \Leftrightarrow ((\operatorname{Coprime}\left(k, x\right)) \land (\sum_{i \in S} k^{i} = x^{2}))$$

*Formalization.* `D5/S1/Digit/ErdosMahlerBinaryDigitSquareRefutation.BinaryBaseSquare` (`✓ std3`).

*Citation.* Paul Erdős (1989). *Some personal and mathematical reminiscences of Kurt Mahler, Australian Mathematical Society Gazette 16(1) (1989), 1–2*. URL: <https://users.renyi.hu/~p_erdos/1989-34.pdf>.

*Commentary.*

For natural k and x and a finite set S of natural exponents, BinaryBaseSquare(k,x,S) means that k and x are coprime and the sum of k^i over i in S equals x squared. The finite set may contain zero, as the source's printed base-7 example does.

**Definition 1.2 (The reported uniqueness suggestion).**

$$(claim) \Leftrightarrow (\forall k \in \mathbb{N}, x \in \mathbb{N}, S \in \operatorname{Finset}\left(\mathbb{N}\right),\; (5 \le k) \Rightarrow \left((1 < x) \Rightarrow \left((\operatorname{BinaryBaseSquare}\left(k, x, S\right)) \Rightarrow (((k = 7) \land (x = 20)) \lor (k = x^{2} - 1))\right)\right))$$

*Formalization.* `D5/S1/Digit/ErdosMahlerBinaryDigitSquareRefutation.claim` (`✓ std3`).

*Citation.* Paul Erdős (1989). *Some personal and mathematical reminiscences of Kurt Mahler, Australian Mathematical Society Gazette 16(1) (1989), 1–2*. URL: <https://users.renyi.hu/~p_erdos/1989-34.pdf>.

*Commentary.*

For every base k at least five, root x greater than one, and finite exponent set S, a binary-digit square is asserted to be either the displayed pair (7,20) or a member of the two-digit family. The subtraction x^2 - 1 is natural-number subtraction.

**Theorem 1.3 (A base-12 counterexample).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/ErdosMahlerBinaryDigitSquareRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/erdos-1989-mahler-binary-digit-square-refutation` (refuted) by `D5/S1/Digit/ErdosMahlerBinaryDigitSquareRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"erdos-1989-mahler-binary-digit-square-refutation","declaration_gid":"D5/S1/Digit/ErdosMahlerBinaryDigitSquareRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul Erdős (1989). *Some personal and mathematical reminiscences of Kurt Mahler, Australian Mathematical Society Gazette 16(1) (1989), 1–2*. URL: <https://users.renyi.hu/~p_erdos/1989-34.pdf>.

*Commentary.*

The identity 12^5 + 12^4 + 12^3 + 12^2 + 1 = 521^2 gives a coprime pair outside both alternatives. A second example is 8^9 + 8^7 + 8^5 + 8^4 + 8^3 + 8^2 + 8 + 1 = 11677^2. Neither example addresses Mahler's fixed-base finiteness conjecture.

## References

- Truth anchor: `D5/S1/Digit/ErdosMahlerBinaryDigitSquareRefutation.BinaryBaseSquare`
- Truth anchor: `D5/S1/Digit/ErdosMahlerBinaryDigitSquareRefutation.claim`
- Truth anchor: `D5/S1/Digit/ErdosMahlerBinaryDigitSquareRefutation.result`
