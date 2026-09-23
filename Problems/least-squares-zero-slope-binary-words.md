---
slug: least-squares-zero-slope-binary-words
bibkey: wiseman2023a222955
doi: null
url: https://oeis.org/A222955
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/LeastSquaresBinaryFit.result
---

# Zero Slope Fits a Sample Best Exactly When Its Weighted Index Sum Is Balanced

## Problem

OEIS A222955, by R. H. Hardin, Mar 10 2013:

> Number of n X 1 0..1 arrays with every row and column least squares fitting to a zero slope
> straight line, with a single point array taken as having zero slope.

The comment carrying the question, by Gus Wiseman, Jan 07 2023:

> Conjecture: A binary word is counted iff it has the same sum of positions of 1's as its reverse,
> or, equivalently, the same sum of partial sums as its reverse.

The companion entry OEIS A359402, which lists the numbers whose binary expansion satisfies the
position condition, repeats the same bridge in its own comments:

> Conjecture: Also numbers whose binary expansion has as least squares fit a line of zero slope,
> counted by A222955.

## Motivation

The frozen theorem `D5/S3/Combinatorics/LeastSquaresBinaryFit.result` settles the comment, and in
the generality of arbitrary finite rational samples, since nothing in the argument uses that the
values are zero or one.

## Gap

Issue 9551 records the screen carried out before the work. Neither A-number appears under
`Problems/`, `D5/` or `Library/` in this repository, and neither appears in the three screening
records. A359402 appears as one `note-only` row in the 2026-09-10 triage record in `Library/Words/`,
where the row was set aside because at length one the best fitting line is not unique. That
disposition is reversed here, and the source itself is what reverses it: the NAME of A222955
declares a single point array to have zero slope, so the degenerate length has a fixed reading, and
stating optimality as attainment rather than as uniqueness of the minimiser matches it. A web query
over both A-numbers together with the least squares phrasing returned no paper or note giving the
equivalence. Citation indices were not exhaustively reachable, so this is a bounded negative
finding.

## Route

An `n X 1` array is a binary word written as a column. Its rows are single entries, which the
entry's own convention gives zero slope, so the rows impose nothing; the condition is on the column.
Let `w` and `S` be the sum of the values and the position-weighted sum, `bb = w / n` the mean value,
`ib = (n + 1) / 2` the mean position, `d_i = b_i - bb`, `u_i = i - ib`, and

    U = Σ u_i ^ 2,        C = Σ d_i * u_i.

**One.** For any intercept `α` and slope `β`, put `γ = bb - α - β * ib`. Each residual is then
`b_i - α - β * i = d_i - β * u_i + γ`. Squaring, summing, and using `Σ d_i = 0` and `Σ u_i = 0` to
kill the two terms linear in `γ`,

    E(α, β)  -  Σ d_i ^ 2  =  β ^ 2 * U  +  n * γ ^ 2  -  2 * β * C.

**Two.** If `C = 0` the right side is `β ^ 2 * U + n * γ ^ 2`, a sum of squares with nonnegative
coefficients, and `E(bb, 0) = Σ d_i ^ 2` exactly. So the zero slope line at the mean attains the
minimum.

**Three.** If `C ≠ 0` then `n ≥ 2`, since at `n = 1` the single centred position is zero and forces
`C = 0`. With `n ≥ 2` the term of `U` at the first index is `((1 - n) / 2) ^ 2 > 0` and every term
is nonnegative, so `U > 0`. Taking `β = C / U` and `γ = 0` makes the right side `- C ^ 2 / U`, which
is negative. Every zero slope line has error at least `Σ d_i ^ 2`, again by step one with `β = 0`,
so no zero slope line is optimal.

**Four.** `C = Σ (b_i - bb) * (i - ib) = S - ib * w`, so `C = 0` is exactly `2 * S = (n + 1) * w`.
For a binary word that says the positions of the ones sum to the same value before and after
reversal, since reversal sends position `i` to `n + 1 - i` and so sends `S` to `(n + 1) * w - S`.

The identity in step one is where the content sits; both directions are read off from it.

## Falsifier

The statement would fail if optimality were read as uniqueness of the minimiser. At `n = 1` one
point is fitted exactly by every line through it, so no line is the unique minimiser and the phrase
names no truth value, while the position condition reads `2 * b_1 = 2 * b_1` and holds. The entry
forecloses that reading in its NAME by declaring a single point array to have zero slope, and the
formal statement matches by asking for a zero slope line that attains the minimum.

Reading the fit against the points `(i, b_i)` with positions counted from zero rather than from one
would shift `ib` and give a different condition; the comment's phrase "positions of 1's" and the
reversal identity pin positions starting at one.

## Evidence

Counting the binary words of length `n` that satisfy `2 * S = (n + 1) * w` gives

    2, 2, 4, 4, 8, 8, 20, 18, 52, 48, 152, 138, 472, 428, 1520, 1392

for `n = 1` through `16`, reproducing the entry's first sixteen terms.

Independently of the counting, the position condition was compared against the rational computation
of the regression cross term for every `n` up to `3 * 10 ^ 5`, with no disagreement. The two words
of length one were checked apart, and both sides hold for each.

## Triage

`theorem`; Tier 1 named external open question, preregistered in issue 9551 before the work. The
computational use is `none`: no declaration is a bounded enumeration, a checker, a numeric reduction
or a certified instance, and the delivered statement is universally quantified over every length and
every rational sample.

## ASSUMED-UNVERIFIED

The literature screen is bounded. Both entries were read in full and record no proof and no
reference to one; the comment has stood on A222955 since January 2023 and is repeated on A359402.
Citation indices and printed sources were not exhaustively reachable, so no worldwide priority claim
is made. The weight is stated plainly: the argument is elementary linear regression, and what is
settled is that the sentence sat on the entry unjudged.
