---
bibkey: erdos1989mahler
authors: Paul Erdős
year: 1989
title: "Some personal and mathematical reminiscences of Kurt Mahler, Australian Mathematical Society Gazette 16(1) (1989), 1–2"
doi: null
url: https://users.renyi.hu/~p_erdos/1989-34.pdf
claim: "He told me about his last paper. Let e_i = 0 or 1. Then Σ_{i=1}^{n} e_i k^i = x^2 has infinitely many solutions for k = 2, 3 and 4. He conjectured that it has only a finite number of solutions for k > 4. In fact, the only nontrivial solution he found was 7^3 + 7^2 + 7 + 1 = 20^2, and perhaps there are no others (1 + (k^2 − 1) = k^2 counts as trivial)."
strata_touched:
  - D5/S1/Digit/ErdosMahlerBinaryDigitSquareRefutation
license: citation-only
triage: anchor
---

# Erdős's reminiscence of Mahler's binary-digit square problem

Erdős reports Mahler's fixed-base finiteness conjecture and the suggestion
that the displayed base-7 square could be the only nontrivial example. The
formal result attached to this note refutes only the latter suggestion.

## Verified locator

- URL: https://users.renyi.hu/~p_erdos/1989-34.pdf
- Locator: page 2 of the Rényi PDF; zbMATH document 4101128.
- Remark (verbatim): He told me about his last paper. Let e_i = 0 or 1. Then Σ_{i=1}^{n} e_i k^i = x^2 has infinitely many solutions for k = 2, 3 and 4. He conjectured that it has only a finite number of solutions for k > 4. In fact, the only nontrivial solution he found was 7^3 + 7^2 + 7 + 1 = 20^2, and perhaps there are no others (1 + (k^2 − 1) = k^2 counts as trivial).
- Reading: the exponent set includes 0 because the printed example contains
  `k^0 = 1`, despite the displayed summation beginning at `i = 1`.
- Reading: "trivial" is the two-digit family `x^2 = k + 1`, equivalently
  `k = x^2 − 1`, matching Erdős's parenthetical
  `1 + (k^2 − 1) = k^2` after renaming the base variable.
- Reading: the coprimality condition `gcd(k, x) = 1` is inherited from
  Mahler's setting and excludes the digit-shift scalings `x ↦ k·x`.
- Background: Kurt Mahler, "The representation of squares to the base 3,"
  *Acta Arithmetica* 53 (1989), 99–106,
  DOI 10.4064/aa-53-1-99-106.
- Corroborating source: the 1988 Mahler letter reproduced in the introduction
  to the 2019 *Kurt Mahler: Selecta* says that base 5 had yielded no example
  and records the base-7 example with root 20.

Only the words "perhaps there are no others" are refuted, by
`12^5 + 12^4 + 12^3 + 12^2 + 1 = 521^2`; a second example is
`8^9 + 8^7 + 8^5 + 8^4 + 8^3 + 8^2 + 8 + 1 = 11677^2`. Neither example
belongs to the trivial family under either reading, and Mahler's fixed-base
finiteness conjecture is untouched. No historical-priority claim is made for
either counterexample.
