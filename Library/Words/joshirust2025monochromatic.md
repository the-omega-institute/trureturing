---
bibkey: joshirust2025monochromatic
authors: Gandhar Joshi and Dan Rust
year: 2025
title: Monochromatic arithmetic progressions in the Fibonacci, Thue-Morse, and Rudin-Shapiro words
doi: 10.1016/j.tcs.2025.115391
url: https://arxiv.org/html/2501.05830v2
claim: Conjecture 4.24 gives (A(d)-1)/d < sqrt(5)/tau for every positive d; Conjecture 3.19 gives i(F_(2n+1))=F_(2n+3)-2 and i(F_(2n))=F_(4n)-1 for every n>=1; Conjecture 3.8 gives the first longest Thue-Morse progression starts at differences 2^e+1 and 2^e-1, contextually for every e>=2.
strata_touched:
  - D5/S1/Words/FibonacciMapBound
  - D5/S1/Words/FibonacciMapFirstStart
  - D5/S1/Words/ThueMorseMapFirstStart
license: citation-only
triage: anchor
---

# Monochromatic progressions in the Fibonacci and Thue-Morse words

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

## First starts at Thue-Morse power-of-two differences

Section 3.2.2, Conjecture 3.8 states
`i(2^n+1)=3·2^(2n)-2^n-1`,
`i(2^(2n)-1)=3·2^(4n)-2^(2n)+1`, and
`i(2^(2n+1)-1)=2^(2n+1)-1`.
The display omits parameter ranges. The contextual reading uses `n>=2`
for the first equation and `n>=1` for the other two, from the preceding
maximum-length statements. Equivalently, for every `e>=2`, with `q=2^e`,
the first start is `3q^2-q-1` at difference `q+1`, `3q^2-q+1` at difference
`q-1` with even `e`, and `q-1` at difference `q-1` with odd `e`.
The known `i(3)=45` excludes the plus-family extension to `e=1`; it is a
previously known boundary exception, not a new refutation.

The word is zero-indexed binary digit parity, beginning `0110100110010110`;
false denotes 0 and true denotes 1. The module
`D5/S1/Words/ThueMorseMapFirstStart` reuses `thueMorse` and binary identities
from `D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd`. Its `MAP` refers to
actual letters. Its `FirstLongest` requires a positive attained length,
a global bound over every natural start and either letter, and exclusion
of that length at all earlier starts. The theorem `result : claim` proves
the complete contextual conjunction, with lengths `q+2`, `q+4`, and `q`.
It is a proof for all `e>=2`, not a finite-exponent verification.

Recognition and the already known maximum lengths are due to I. Aedo,
U. Grimm, Y. Nagai and P. Staynova, *Monochromatic arithmetic progressions
in binary Thue-Morse-like words*, Theoretical Computer Science 934 (2022),
65–80, cited as [2] by Joshi and Rust. Lemma 15 supplies recognition;
Propositions 16–17 supply the maxima. The new first-start argument proves
the needed binary recognition, carry/borrow exclusions, bounds and
attainment internally; these prerequisites are not additional settlements.

The bounded audit recorded on 5 October 2026 in
https://github.com/the-omega-institute/trureturing/issues/13307 found no
identified exact resolution in the checked adjacent literature, OEIS
A342827, arXiv/OpenAlex and formal-conjectures searches, and repository
ownership checks. The unavailable thesis and unreadable search/index
results supplied no negative evidence. This is not an exhaustive worldwide
priority claim. The exact conjecture is at
https://arxiv.org/html/2501.05830v2#S3.Thmtheorem8.

## Verified locator

- DOI: https://doi.org/10.1016/j.tcs.2025.115391
- URL: https://arxiv.org/html/2501.05830v2
- arXiv: 2501.05830v2; Definitions 2.2-2.3, Proposition 4.1, Lemma 4.2,
  Theorems 4.6 and 4.15, and Conjecture 4.24; Definition 2.5 and
  Conjecture 3.19 at https://arxiv.org/html/2501.05830v2#S3.Thmtheorem19;
  Section 3.2.2, Conjecture 3.8 at
  https://arxiv.org/html/2501.05830v2#S3.Thmtheorem8.
