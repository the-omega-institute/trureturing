# Raw W-Digit Strings

`D5/S1/Digit/Raw` represents raw W-digit strings as finitely supported maps from indices to natural coefficients, so a digit position may temporarily carry coefficients larger than one. Evaluation multiplies each coefficient by the W weight `W_i = Fib (i + 2)` and sums; evaluation is additive.

Canonical strings are the binary, nonadjacent ones. The file bridges canonical strings to the mathlib Zeckendorf representation in both directions, with the index offset `W_i = Fib (i + 2)` stated once at the bridge.

**Illustrative Zeckendorf normalization:** `Z(89) + Z(34) = Z(123) = 1010000000_W` ⟨computed-by-C#; illustrative, not kernel-verified⟩
