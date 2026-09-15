# Yanev's Binary-Reversal Position Identity

## Abstract

Binary reversal is determined by the lexicographic position recurrence after removing the leading bit.

All variables and values lie in the natural numbers. A Boolean bit b and a half-index m represent Nat.bit b m, equal to 2m when b is false and 2m+1 when b is true. The operator binaryRec is Nat.binaryRec. The operator log_2(m) is Nat.log 2 m: for positive m it is the floor of the base-two logarithm, and Mathlib totalizes it at zero. Powers, addition, and multiplication are natural-number operations. Subtraction is truncated natural subtraction, so stripTop(0)=0.

**Definition 1.1 (The A264596 lexicographic position).**

$$w = binaryRec\left(0, (b, m, p) \mapsto if\left(b, p + m + 1, p\right)\right)$$

*Formalization.* `D5/S1/Digit/YanevBinaryReversalPositionIdentity.w` (`✓ std3`).

*Citation.* David W. Wilson; Ralf Stephan; Velin Yanev; Alois P. Heinz; Henry Bottomley (2017). *OEIS A030101, binary digit reversal, with Yanev's position identity*. URL: <https://oeis.org/A030101>.

*Commentary.*

The defining binary recursion starts at zero. An even low bit preserves the previous value; an odd low bit adds the half-index and one. This is Heinz's recurrence for A264596.

**Definition 1.2 (Remove the leading binary bit).**

$$\forall n \in Nat,\; stripTop\left(n\right) = n - 2^{\left(log_{2}\right)\left(n\right)}$$

*Formalization.* `D5/S1/Digit/YanevBinaryReversalPositionIdentity.stripTop` (`✓ std3`).

*Citation.* David W. Wilson; Ralf Stephan; Velin Yanev; Alois P. Heinz; Henry Bottomley (2017). *OEIS A030101, binary digit reversal, with Yanev's position identity*. URL: <https://oeis.org/A030101>.

*Commentary.*

For a positive input, 2 raised to log_2(n) is its largest binary power. Natural subtraction removes that leading power, matching A053645. The definition is totalized at zero.

**Definition 1.3 (Reverse the binary digits).**

$$rev = binaryRec\left(0, (b, m, p) \mapsto if\left(b, if\left(m = 0, 1, p + 2^{(\left(log_{2}\right)\left(m\right) + 1)}\right), p\right)\right)$$

*Formalization.* `D5/S1/Digit/YanevBinaryReversalPositionIdentity.rev` (`✓ std3`).

*Citation.* David W. Wilson; Ralf Stephan; Velin Yanev; Alois P. Heinz; Henry Bottomley (2017). *OEIS A030101, binary digit reversal, with Yanev's position identity*. URL: <https://oeis.org/A030101>.

*Commentary.*

The defining binary recursion uses Stephan's recurrence for A030101. The first odd value is one; subsequent odd steps add the next leading binary power, while even steps preserve the previous value.

**Theorem 1.4 (Yanev's position identity).**

$$\forall n \in Nat,\; (1 \le n) \Rightarrow (rev\left(n\right) + 2 \cdot w\left(stripTop\left(n\right)\right) + 1 = 2 \cdot w\left(n\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/YanevBinaryReversalPositionIdentity.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David W. Wilson; Ralf Stephan; Velin Yanev; Alois P. Heinz; Henry Bottomley (2017). *OEIS A030101, binary digit reversal, with Yanev's position identity*. URL: <https://oeis.org/A030101>.

*Commentary.*

For every positive natural n, moving both subtracted terms to the additive side gives a truncation-free form of Yanev's conjecture. Binary induction tracks stripTop through even and odd inputs and closes both branches from the two source recurrences.

## References

- Truth anchor: `D5/S1/Digit/YanevBinaryReversalPositionIdentity.result`
- Truth anchor: `D5/S1/Digit/YanevBinaryReversalPositionIdentity.rev`
- Truth anchor: `D5/S1/Digit/YanevBinaryReversalPositionIdentity.stripTop`
- Truth anchor: `D5/S1/Digit/YanevBinaryReversalPositionIdentity.w`
