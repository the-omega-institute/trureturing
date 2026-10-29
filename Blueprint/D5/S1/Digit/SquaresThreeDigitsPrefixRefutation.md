# Prefix Closure Fails for Squares with Three Digits

## Abstract

A fifteen-block decimal word has a square with digits in {0,2,5}, but deleting its last block gives a square containing digit one.

**Definition 1.1 (The literal decimal word).**

$$\forall runs \in \operatorname{List}{\mathbb{N}},\; \operatorname{decimalWord}\left(runs\right) = \operatorname{Append}\left(\operatorname{FlatMap}\left(block, runs\right), \operatorname{Singleton}\left(5\right)\right)$$

*Formalization.* `D5/S1/Digit/SquaresThreeDigitsPrefixRefutation.decimalWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each natural entry a, block(a) is the digit 4 followed by exactly a copies of 9. Concatenate those blocks in their listed order and append one final digit 5. Entries equal to zero produce a lone 4. This is the shorthand on page 25 of Geisser, Korner, Kurz and Zahn, Squares with three digits, arXiv:2112.00444v2.

**Definition 1.2 (The ordinary decimal integer).**

$$\forall runs \in \operatorname{List}{\mathbb{N}},\; \operatorname{encode}\left(runs\right) = \operatorname{ofDigits}\left(10, \operatorname{Reverse}\left(\operatorname{decimalWord}\left(runs\right)\right)\right)$$

*Formalization.* `D5/S1/Digit/SquaresThreeDigitsPrefixRefutation.encode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Mathlib's Nat.ofDigits reads least significant digits first, so the literal decimal word is reversed exactly once. No polynomial surrogate or alternative digit predicate enters the definition.

**Definition 1.3 (The actual square digits).**

$$\forall n \in \mathbb{N},\; (\operatorname{GoodSquare}\left(n\right)) \Leftrightarrow (\forall d \in \mathbb{N},\; (\operatorname{In}\left(d, \operatorname{digits}\left(10, n^{2}\right)\right)) \Rightarrow ((d = 0) \lor ((d = 2) \lor (d = 5))))$$

*Formalization.* `D5/S1/Digit/SquaresThreeDigitsPrefixRefutation.GoodSquare` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

GoodSquare tests every digit of the ordinary natural integer square. It requires subset membership in {0,2,5}; it does not require that all three digits occur. The Boolean list test is true exactly when every digit satisfies that membership condition.

**Definition 1.4 (The whole prefix implication).**

$$(claim) \Leftrightarrow (\forall runs \in \operatorname{List}{\mathbb{N}},\; (2 \le \operatorname{length}\left(runs\right)) \Rightarrow ((\operatorname{GoodSquare}\left(\operatorname{encode}\left(runs\right)\right)) \Rightarrow (\operatorname{GoodSquare}\left(\operatorname{encode}\left(\operatorname{dropLast}\left(runs\right)\right)\right))))$$

*Formalization.* `D5/S1/Digit/SquaresThreeDigitsPrefixRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Conjecture 1 on page 26 quantifies over every finite tuple of natural entries of length at least two. There is no bound on entries or length. Deletion removes the last entry and its entire 4/nines block; the final digit 5 remains.

**Definition 1.5 (A fifteen-block tuple).**

$$counterexample = [0,1,3,7,15,31,63,127,2,6,14,62,14,6,2]$$

*Formalization.* `D5/S1/Digit/SquaresThreeDigitsPrefixRefutation.counterexample` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The tuple is [0,1,3,7,15,31,63,127,2,6,14,62,14,6,2]. Its cumulative block lengths are 1,3,7,15,31,63,127,255,258,265,280,343,358,365,368. The full root has 369 decimal digits. Removing the final block leaves a root with 366 decimal digits.

**Theorem 1.6 (Prefix closure is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/SquaresThreeDigitsPrefixRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The full tuple passes the literal square-digit test, while its dropLast tuple fails it. Both assertions are reduced by the Lean kernel. The implication at this tuple therefore contradicts claim. The carry mechanism can be seen from S, the cumulative lengths: N = 5*10^368*(1-sum(10^(-s),s in S)). Write S as {1,3,7,15,31,63,127} union (255+T), where T={0,3,10,25,88,103,110,113}. The four pairs (0,113),(3,110),(10,103),(25,88) have sum 113. In the normalized square N^2/10^738, decimal positions are counted after the decimal point. They contribute four 5s in position 624; their sum 20 carries a 2 into position 623. Deleting 113 leaves three such pairs, whose sum 15 carries a forbidden 1 instead. This refutes the entire universal implication; it makes no assertion of a least counterexample or historical priority.

## References

- Truth anchor: `D5/S1/Digit/SquaresThreeDigitsPrefixRefutation.GoodSquare`
- Truth anchor: `D5/S1/Digit/SquaresThreeDigitsPrefixRefutation.claim`
- Truth anchor: `D5/S1/Digit/SquaresThreeDigitsPrefixRefutation.counterexample`
- Truth anchor: `D5/S1/Digit/SquaresThreeDigitsPrefixRefutation.decimalWord`
- Truth anchor: `D5/S1/Digit/SquaresThreeDigitsPrefixRefutation.encode`
- Truth anchor: `D5/S1/Digit/SquaresThreeDigitsPrefixRefutation.result`
