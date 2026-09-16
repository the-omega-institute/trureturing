---
slug: oeis-a350900-schulte-gcd-quotient-row-sum-convolution
bibkey: schulte2022a350900
doi: null
url: https://oeis.org/A350900
triage: theorem
motivation_gids:
  - D5/S3/ArithSums/SchulteGcdQuotientRowSumConvolution
---

# Schulte's gcd-quotient row-sum convolution

## Problem

OEIS A350900, NAME (`%N`, verbatim):

> Triangle read by rows: T(n, k) = Sum_{i=1..n} gcd(i,n) / gcd(gcd(i,k),n) for 1 <= k <= n.

The settled FORMULA (`%F`, verbatim) is:

> Conjecture: Row sums equal Dirichlet convolution of A002618 and A057660.

The full-quantifier reading is: for every positive natural `n`, define
`rowSum(n) = Sum_{i=1..n} Sum_{k=1..n}
gcd(i,n)/gcd(gcd(i,k),n)`; then

`rowSum(n) = Sum_{d|n} d*phi(d) * (Sum_{e|(n/d)} e*phi(e))`.

Here `phi` is Euler's totient, A002618(n) is `n*phi(n)`, and A057660(n)
is `Sum_{d|n} d*phi(d)`. The identity
`gcd(gcd(i,k),n) = gcd(gcd(i,n),k)` shows the denominator of each row
summand divides its numerator; these are exact natural quotients. For each
`d|n` the complementary quotient `n/d` is also exact. Only the quoted
row-sum formula is settled. The `%C` conjecture for an arbitrary arithmetic
function `f` is outside this claim.

## Motivation

The two-level gcd quotient reduces, for fixed `i`, to a periodic sum in
`k` whose divisor fibres have totient cardinalities. Applying the same
totient count to the outer gcd fibres exposes the two convolution factors.

## Gap

OEIS A350900 continues to mark the row-sum formula as a conjecture and gives
no proof. OEIS A373059 identifies the same double sum as the row sums of
A350900. Seiichi Manyama recorded the equivalent formula in revision 11 on
May 24, 2024, at 11:06:04 EDT
(https://oeis.org/history?seq=A373059):

`Sum_{d|n} phi(n/d) * (n/d) * sigma_2(d^2)/sigma(d^2)`.

The equivalence follows from the A057660 formula
`sigma_2(m^2)/sigma(m^2) = Sum_{e|m} e*phi(e)`. The A373059 formula is prior
documentation of the equivalent identity. This dossier makes no
first-discovery, first-resolution, or historical-priority claim.

Tóth's 2010 gcd-sum survey records Cesàro's general fibre formula
`Sum_{k=1..n} f(gcd(k,n)) = Sum_{d|n} f(d)*phi(n/d)` and the A057660 divisor
sum. These general results supply the established background for the proof,
but the survey does not state the nested A350900 identity.

As of September 16, 2026, the complete inspected A350900 history
(13 revisions), the complete inspected A373059 history (19 revisions),
Tóth's 2010 survey
(https://cs.uwaterloo.ca/journals/JIS/VOL13/Toth/toth10.html),
arXiv:2110.07271, arXiv:1306.1020, and Bordellès's 2015 *Journal of Integer
Sequences* paper
(https://cs.uwaterloo.ca/journals/JIS/VOL18/Bordelles/bord21.pdf) yielded no
complete prior proof of the target identity. The literature result is
`not-found-in-searched-scope`, never a claim that the proof is globally novel.

No equal or stronger theorem was found in the current repository or pinned
Mathlib. The repository's other gcd-sum results concern different summands,
and pinned Mathlib supplies the totient, divisor-reindexing, periodic-gcd, and
finite-fibre lemmas used by the proof rather than the target identity.

## Route

1. Rewrite `gcd(gcd(i,k),n)` as `gcd(gcd(i,n),k)` and rotate the
   `1..n` sums to complete residue ranges; endpoint equality follows
   from gcd periodicity.
2. With `g=gcd(i,n)`, a local calculation inside `result` establishes
   `Sum_{k in range(n)} g/gcd(g,k) = (n/g)*Sum_{f|g} f*phi(f)`.
   Periodicity splits `n` into `n/g` blocks of length `g`. Grouping a
   block's `k` by `gcd(g,k)` gives totient cardinalities for the
   complementary divisors; reindexing produces the divisor sum.
3. Stratify the outer `i` by `gcd(n,i)=g`, giving `phi(n/g)` indices
   for each `g|n`. Reindex the complementary divisors by `d=n/g`
   to obtain the inlined A057660 convolution factor.

The public result has `proof_shape: bind-only`, no escape witness, and
`admission_basis: open-problem-resolution`. It is the sole public theorem in
this module and settles exactly the quoted named conjecture; the admission
classification is not a claim to the first proof or first resolution.
Registration issue #8240 was created at 2026-09-16T01:17:03Z, before the first
proof probe at 2026-09-16T01:18:31.892Z. The proof directly reuses pinned
Mathlib statements through instantiation, finite-fibre regrouping, divisor
reindexing, and normalization. There is no direct frozen D5 dependency; all
supporting facts remain local `have` terms inside `result`.

`utility: none` applies because `rowSum` is a symbolic definition and `result`
is an unbounded symbolic identity, not a bounded enumeration, checker, numeric
reduction, or certified finite instance.

## Falsifier

Any positive natural `n` with unequal sides of the displayed convolution
would refute the result. An `i,k` in `1..n` for which
`gcd(gcd(i,k),n)` fails to divide `gcd(i,n)` would refute the claimed
exactness of a summand.

## Evidence

The Lean definition `rowSum` transcribes the A350900 double sum with natural
division. The theorem `result` retains the hypothesis `0 < n` and proves only
the displayed divisor convolution. Its proof establishes the fixed-gcd fibre
identity locally for every outer index and then groups the outer indices by
their gcd with `n`.

The proof uses the standard three permitted axioms through Mathlib. Its direct
imports supply the totient/divisor identities and interval-sum conversion.
No statement about an arbitrary arithmetic function occurs in the public
surface.

## Triage

`theorem`; the formal target is exactly the quoted `%F` row-sum formula over
all positive natural row indices.

## ASSUMED-UNVERIFIED

The literature search is not a proof of historical novelty. A057660 revisions
63 through 1 were not inspected. The Gould-Shonhiwa 1997 full texts, Tóth's
1998 regular-convolution paper, some cyclic-group sources, and the U338
solution were not obtained. A complete prior proof outside the searched scope
remains ASSUMED-UNVERIFIED. No priority claim is made. The arbitrary-function
conjecture in A350900 is outside the formal statement and remains unresolved
by this result.
