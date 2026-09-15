---
slug: oeis-a105595-barry-triangle-row-sums-odd
bibkey: barry2005a105595
doi: null
url: https://oeis.org/A105595
triage: theorem
motivation_gids:
  - D5/S3/ArithSums/BarryTriangleRowSumsOdd
---

# Every row sum of the A105594 triangle is odd

## Problem

OEIS A105595, NAME (`%N`, verbatim):

> Row sums of number triangle A105594.

Its COMMENT conjecture (`%C`, verbatim) is:

> Conjecture : all terms are odd.

Its FORMULA (`%F`, verbatim) is:

> a(n)=sum{k=0..n, mod(sum{j=0..n, abs(mu(binomial(n, j)))*mod(binomial(j, k), 2)}, 2)}

OEIS A105594, FORMULA (`%F`, verbatim):

> T(n, k) = mod(Sum_{j=0..n}(abs(mu(binomial(n,j)))*mod(binomial(j,k),2)), 2).

The literal proved statement defines
`rowEntry n k = (sum j in range (n+1), abs(mu(choose n j)) *
(choose j k mod 2)) mod 2`, defines
`rowSum n = sum k in range (n+1), rowEntry n k`, and proves
`forall n : Nat, Odd (rowSum n)`.

The following are not claimed:

- any other property of A105594;
- equivalence between the `%N` matrix-product phrasing
  `abs(A103447)*A047999 mod 2` and the displayed `%F` sum;
- exhaustive literature coverage or a priority claim.

The delivery formalizes the two displayed `%F` sums and discloses that source
choice rather than identifying the matrix-product description with them.

## Motivation

The conjecture is present from revision 1 in 2005 and remains labelled
Conjecture in 2026, a span of 21 years. A universal parity theorem settles the
explicit row-sum formula for every natural row index.

## Gap

On 2026-09-15, the probe recorded the following bounded search outcomes:

> Literature: read all 5 A105595 revisions and all 21 A105594 revisions; neither history contains a settlement. arXiv exact-ID and shape queries each returned no results; Crossref exact IDs returned 0 and its shape/Paul-Barry queries yielded no matching theorem. OpenAlex autocomplete returned 0 for each ID and the Mobius/Pascal shape; its four squarefree-binomial hits were Granville-Ramare/Stanica and unrelated. The apparent 2026 SSRN title hit (10.2139/ssrn.7215159) was ruled out by its Crossref abstract and OpenAlex DOI record.

> Search limitations: OpenAlex full works-search remained HTTP 429 (10 credits required, 3 remaining), and Semantic Scholar returned HTTP 429. Those two readings remain `ASSUMED-UNVERIFIED`; the literature claim is bounded, not exhaustive.

A search of the repository at the preregistration base found zero occurrences
of A105595, A105594, the proposed module name, or the Barry bibkey. A search of
the pinned Mathlib supplied the named finite-sum and cast lemmas but no theorem
settling the OEIS statement. These checked surfaces do not establish
exhaustive literature coverage, and no priority claim is made.

## Route

1. Cast each already reduced inner sum to `ZMod 2`. The identity
   `ZMod.natCast_mod` justifies replacing the cast of `x mod 2` by the cast of
   `x`; only after this step does `Finset.sum_comm` interchange the finite
   `j` and `k` sums.
2. For fixed `j`, `Nat.choose_eq_zero_of_lt` kills the terms with `k > j`.
   Then `Nat.sum_range_choose` identifies the remaining Pascal row sum as
   `2^j`.
3. Modulo two, every term with `j > 0` vanishes. At `j=0`,
   `Nat.choose n 0 = 1` and
   `ArithmeticFunction.moebius_apply_one` gives
   `abs(mu(1)) = 1`, so the row sum is congruent to one modulo two.

After the local steps are inlined, the proof is bind-only over these pinned
Mathlib facts: it consists of direct instantiation, finite-sum rearrangement,
projection, and normalization.

## Falsifier

Any natural `n` for which the explicit `%F` row sum is even would contradict
`result`. A mismatch between the displayed `%F` sum and the matrix-product
description of A105594 would instead falsify the excluded source equivalence,
not the kernel theorem delivered here.

## Evidence

- Lean module: `D5/S3/ArithSums/BarryTriangleRowSumsOdd.lean`.
- Main theorem: `result`, with std3 axiom closure
  `[propext, Classical.choice, Quot.sound]`.
- The definitions `rowEntry` and `rowSum` have the same std3 axiom closure.
- Kernel profile on this worktree: wall time 3.41 seconds, type checking
  5.6 milliseconds, and maximum resident set size 1,723,826,176 bytes.
- Deleting `Mathlib.Data.ZMod.Basic` makes the module exit 1; deleting
  `Mathlib.NumberTheory.ArithmeticFunction.Moebius` also makes it exit 1.
- The literal `%F` scan for `n=0` through `n=120` found all 121 row sums odd,
  with maximum row sum 47.
- The bounded scan carries no proof; the Lean theorem carries the universal
  statement.

## Triage

`theorem`. Barry's parity conjecture is proved for every natural `n`; the
resolution is `proved`, not `refuted`.

## ASSUMED-UNVERIFIED

Literature completeness outside the checked OEIS histories, arXiv, Crossref,
OpenAlex surfaces, Semantic Scholar response, pinned Mathlib, and repository
searches is unverified. The OpenAlex full works-search and Semantic Scholar
query were not completed because both returned HTTP 429. The bounded scan does
not establish the universal statement. No matrix-product equivalence,
exhaustive-search conclusion, or priority claim is made.
