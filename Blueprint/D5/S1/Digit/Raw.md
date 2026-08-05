# Raw W-Digit Strings

## Abstract

Raw W digits bridge finite multiplicities to mathlib Zeckendorf lists.

`D5/S1/Digit/Raw` represents raw W-digit strings as finitely supported maps from indices to natural coefficients, so a digit position may temporarily carry coefficients larger than one. Evaluation multiplies each coefficient by the W weight `W_i = Fib (i + 2)` and sums; evaluation is additive.

Canonical strings are the binary, nonadjacent ones. The file bridges canonical strings to the mathlib Zeckendorf representation in both directions, with the index offset `W_i = Fib (i + 2)` stated once at the bridge.

**Example 1.1 (Illustrative Zeckendorf normalization).**

$$
\operatorname{Z}\left(89\right) + \operatorname{Z}\left(34\right) = \operatorname{Z}\left(123\right) = 1010000000_{W}
$$

*Source.* Repository-derived.

*Commentary.*

This illustrative normalization is derived by the repository's deterministic W-digit computation.

## References

- Dependency: [D5/S0/Conventions/WDigits](../../S0/Conventions/WDigits.md)
