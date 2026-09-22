---
bibkey: joshirust2025monochromatic
authors: Gandhar Joshi and Dan Rust
year: 2025
title: Monochromatic arithmetic progressions in the Fibonacci, Thue-Morse, and Rudin-Shapiro words
doi: 10.1016/j.tcs.2025.115391
url: https://arxiv.org/html/2501.05830v2
claim: Conjecture 4.24 gives (A(d)-1)/d < sqrt(5)/tau for every positive d; Conjecture 3.19 gives i(F_(2n+1))=F_(2n+3)-2 and i(F_(2n))=F_(4n)-1 for every n>=1.
strata_touched:
  - D5/S1/Words/FibonacciMapBound
  - D5/S1/Words/FibonacciMapFirstStart
license: citation-only
triage: anchor
---

# Monochromatic progressions in the Fibonacci word

Joshi and Rust, *Theoretical Computer Science* 1050 (2025), 115391,
Definitions 2.2 and 2.3 define a monochromatic arithmetic progression at
any nonnegative start and its global maximum length at a fixed difference.
Proposition 4.1 and Lemma 4.2 identify the Fibonacci letters with the
fractional orbit at index one greater than the word index. Theorems 4.6 and
4.15 give the two exact maximum-length regimes using the step distance
`g(d)=min({d tau},1-{d tau})`. These are published prerequisites, not the
strict global inequality: Conjecture 4.24 states that for every integer
`d >= 1`, `(A(d)-1)/d < sqrt(5)/tau`.

## First starts at Fibonacci differences

Definition 2.5 defines `i(d)` as the earliest nonnegative position at which
a progression of the global maximum length `A(d)` begins, allowing either
symbol. Conjecture 3.19 states the conjunction
`i(F_(2n+1))=F_(2n+3)-2` and `i(F_(2n))=F_(4n)-1`.
The author's A364648 comment supplies the domain `n > 0`:
https://oeis.org/search?q=id:A364648&fmt=text.
The word convention is the zero-indexed fixed point of `0 -> 01, 1 -> 0`;
the repository's true letter denotes 0. The mechanical phase is at word
index plus one.

The theorem `D5/S1/Words/FibonacciMapFirstStart.result` proves the exact
all-positive-index conjunction. Its first-start definition minimizes starts
attaining the existing `goldenMAPMaximum`, not a formula-defined maximum.
Boundedness, attainment and the exclusion of maximal false-letter runs are
established in the proof. The published Conjecture 4.24 account above remains
separate.

The bounded literature audit through 17 September 2026 found no later
proof or refutation of Conjecture 3.19. This is not an exhaustive worldwide
priority claim. The thesis reading is oracle-reported; direct caller HTTP
access returned 403 and did not independently verify it.

## Verified locator

- DOI: https://doi.org/10.1016/j.tcs.2025.115391
- URL: https://arxiv.org/html/2501.05830v2
- arXiv: 2501.05830v2; Definitions 2.2-2.3, Proposition 4.1, Lemma 4.2,
  Theorems 4.6 and 4.15, and Conjecture 4.24; Definition 2.5 and
  Conjecture 3.19 at https://arxiv.org/html/2501.05830v2#S3.Thmtheorem19.
