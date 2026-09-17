---
slug: erdos-1989-mahler-binary-digit-square-refutation
bibkey: erdos1989mahler
doi: null
url: https://users.renyi.hu/~p_erdos/1989-34.pdf
triage: theorem
motivation_gids:
  - D5/S1/Digit/ErdosMahlerBinaryDigitSquareRefutation
---

# Refutation of Erdős's report of Mahler's binary-digit square uniqueness

## Problem

Erdős's 1989 reminiscence, page 2 (verbatim):

> He told me about his last paper. Let e_i = 0 or 1. Then Σ_{i=1}^{n} e_i k^i = x^2 has infinitely many solutions for k = 2, 3 and 4. He conjectured that it has only a finite number of solutions for k > 4. In fact, the only nontrivial solution he found was 7^3 + 7^2 + 7 + 1 = 20^2, and perhaps there are no others (1 + (k^2 − 1) = k^2 counts as trivial).

The literal refuted statement is the proposition `claim`:

```text
∀ (k x : ℕ) (S : Finset ℕ),
  5 ≤ k → 1 < x → BinaryBaseSquare k x S →
    (k = 7 ∧ x = 20) ∨ k = x ^ 2 - 1
```

Here `BinaryBaseSquare k x S` means
`Nat.Coprime k x ∧ ∑ i ∈ S, k ^ i = x ^ 2`. The exponent set includes zero
because the printed example contains `k^0 = 1`. "Trivial" means the two-digit
family `x^2 = k + 1`, equivalently `k = x^2 − 1`, matching Erdős's
parenthetical after renaming the base variable. The coprimality condition
`gcd(k, x) = 1` comes from Mahler's setting and excludes digit-shift scalings
`x ↦ k·x`. The counterexamples `(12, 521)` and `(8, 11677)` are in no trivial
family under either reading.

This refutation makes no claim about Mahler's finiteness conjecture for any
fixed `k > 4` and no claim about infinitude for `k = 2, 3, 4`.

## Motivation

The source presents the base-7 identity as Mahler's only known nontrivial
example and immediately suggests that no others may exist. A single explicit
coprime square outside the displayed and trivial families resolves that
literal universal uniqueness statement.

## Gap

Preregistration issue #7658 and its probe report record searches dated
September 14, 2026. Both pages of the Rényi PDF and the zbMATH record 4101128
were checked. The introduction to the 2019 *Kurt Mahler: Selecta* reprints a
1988 letter describing no base-5 example and the base-7 square, without a
later solution. A zbMATH reference-text back-search for the Erdős note returned
three citing works, Baake–Borwein–Bugeaud–Coons (2019), Steuding (2016), and
Elkies–Goel (2023); none concerns 0/1-digit squares.

An arXiv exact-title search returned 0 results, as did an arXiv search for
`11677 Mahler`. MathOverflow returned 0 results. GitHub searches for the exact
phrase, `BinaryBaseSquare`, and `521^2 12^5` each returned 0 results. Crossref
returned only Mahler's 1989 background-paper record. The problem was not
listed on erdosproblems.com. OEIS value searches for
`1,8,64,512,4096,11677` and `1,12,144,521,1728` were empty. OEIS A342546
lists 11677 in the different framing "least square with exactly n ones in
base n," and A176189 concerns base 3 only.

OpenAlex `/works` returned HTTP 429, Semantic Scholar returned HTTP 429, and
Google Scholar and MathSciNet were not checked; these surfaces are
`ASSUMED-UNVERIFIED`. The bounded search does not establish exhaustive
literature coverage, and no historical-priority claim is made for `(12, 521)`.

## Route

The finite certificate first proves `Nat.Coprime 12 521` and
`12^5 + 12^4 + 12^3 + 12^2 + 1 = 271441 = 521^2`. It therefore supplies
`BinaryBaseSquare 12 521 {0, 2, 3, 4, 5}`. Instantiating `claim` at this triple
leaves two alternatives. The base is not 7 and the root is not 20, while
`12 ≠ 521^2 − 1`; hence both alternatives are impossible.

## Falsifier

A proof of `claim` would falsify this refutation. The checked base-12
certificate proves its negation, so such a proof would contradict the formal
result at the explicit instance `(12, 521, {0, 2, 3, 4, 5})`.

## Evidence

- Lean module:
  `D5/S1/Digit/ErdosMahlerBinaryDigitSquareRefutation.lean`.
- Main theorem: `result : ¬ claim`, with exactly the std3 axioms `propext`,
  `Classical.choice`, and `Quot.sound`.
- The Stage B hot-tree profile measured 7.28 seconds wall time, 1.87 ms
  cumulative type checking, and maximum resident set size 1,468,006,400 bytes.
- The probe profile measured 6.26 seconds wall time, 2.02 ms cumulative type
  checking, and maximum resident set size 1,468,432,384 bytes, with the same
  std3 axiom closure.
- The orchestrator independently checked
  `521^2 = 271441 = 12^5 + 12^4 + 12^3 + 12^2 + 1`, the base-12 digit string
  `111101`, and primality of 521.
- The orchestrator independently checked
  `11677^2 = 136352329 = 8^9 + 8^7 + 8^5 + 8^4 + 8^3 + 8^2 + 8 + 1`
  and primality of 11677.
- Its complete bounded enumeration of nontrivial coprime solutions with
  `5 ≤ k ≤ 40` and `2 ≤ x ≤ 200000` returned exactly `(7, 20)`, `(8, 11677)`,
  and `(12, 521)`.
- Its base-12 root search through 300000 returned exactly
  `1, 12, 144, 521, 1728, 6252 = 12·521, 20736, 75024 = 144·521, 248832`.
- The probe independently reproduced the base-12 certificate and the same
  theorem, declaration, axiom, and profile readings recorded above.

The bounded computations beyond the formal `(12, 521)` certificate are
supporting evidence only. They do not strengthen the theorem's universal
negation or establish a classification.

## Triage

`theorem`. The explicit coprime base-12 square refutes the literal uniqueness
remark. Mahler's fixed-base finiteness conjecture remains untouched.

## ASSUMED-UNVERIFIED

OpenAlex and Semantic Scholar were rate-limited with HTTP 429. Google Scholar
and MathSciNet were not checked. The literature search and the enumerations
over `5 ≤ k ≤ 40`, `2 ≤ x ≤ 200000`, and base-12 roots through 300000 are
bounded; they establish neither exhaustive coverage nor historical priority.
