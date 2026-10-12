---
slug: bhattacharjee-mandal-bhattacharya-2026-union-closed-count-refutation
bibkey: bhattacharjee2026unionclosed
doi: 10.48550/arXiv.2610.02833
url: https://arxiv.org/abs/2610.02833v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/ErdosUlam/UnionClosedCountRefutation.result
---

# The proposed union-closed counting threshold is false

## Problem

Bhattacharjee–Mandal–Bhattacharya, arXiv:2610.02833v1, Question 9.2:

> Is there a constant C such that U(n,N) < 2^{N−1} for all large n and all N ≥ n^{C log₂ log₂ n}?

Proposition 5.4 defines the labelled count and its proposed application:

> Let U(n,N) be the number of union-closed families ℱ ⊆ 2^[n] with |ℱ| = N. If U(n,N) < 2^{N−1}, then F(n) < N.

Section 1 defines union-closed by requiring A ∪ B ∈ ℱ whenever A,B ∈ ℱ.
The Lean definition counts finite families of subsets of `Fin n`, with no
quotient by ground-set permutations. The claim quantifies over a real constant
C, a natural cutoff, every dimension above that cutoff, and every natural N
meeting the real-power threshold. Its result is the literal negation of that
claim. The logarithms and real power are Mathlib's total functions; the proof
uses only dimensions at least 24, where both logarithms have positive
arguments and the usual interpretation applies.

## Motivation

The proposed estimate would combine with Proposition 5.4 to bound the
union-closed extremal function at a quasipolynomial scale. A failure of the
counting estimate prevents this universal counting route, without settling
the extremal problem itself.

## Gap

This counting assertion is Question 9.2 of Bhattacharjee–Mandal–Bhattacharya,
arXiv:2610.02833v1, the only version. A positive answer would give
$F(n) < n^{C\log_2\log_2 n}$ via their Proposition 5.4. The Erdős Problems
forum thread for #1183 does not address this counting assertion. Chojecki's preprint proves ⌈(n+1)/2⌉ ≤ F(n) ≤ n^{log₂ n + O(log log n)} and ⌈(n+1)/2⌉ ≤ f(n) ≤ (3+o(1)) n log₂² n; its closing questions ask for the order of growth of f(n) and F(n) and about union-closed families of bounded free rank; it does not consider the counting assertion of Question 9.2. MathDB title and author searches find no entry.

## Route

For r ≥ 4 put n = 6r and

$$
B=\binom{6r}{r},\qquad H=\sum_{i=0}^{r-1}\binom{6r}{i},\qquad
q=\lfloor B/4\rfloor,\qquad N=H+q.
$$

There are B subsets of size 5r, by complementation. Embed q disjoint
quadruples into that level. For each of the 4^q functions choosing one member
of each quadruple, include the q chosen sets and all subsets of size greater
than 5r. Every strict superset of a chosen set lies in the upper tail, so the
family is upward-closed and therefore union-closed. Complementation shows
that the upper tail has exactly H members. Each family has size N; different
choice functions give different families. Thus 4^q ≤ U(6r,N).

For each i < r the binomial recurrence gives

$$
(5r+1)\binom{6r}{i}
\le (6r-i)\binom{6r}{i}
=(i+1)\binom{6r}{i+1}
\le r\binom{6r}{i+1}.
$$

Summing and shifting the index gives (4r+1)H ≤ r(B−1).
Since r ≥ 1, this implies 4H < B and H ≤ q. Consequently

$$
2^N\le 2^{2q}=4^q\le U(6r,N).
$$

Vandermonde's identity, using the term that chooses one point from an added
six-point block, gives B ≥ 6^r by induction. Since 3^r ≥ 4 for r ≥ 4,
4·2^r ≤ 6^r ≤ B, hence q ≥ 2^r and N ≥ 2^r.
This is stronger than the size estimate needed in the counting route.

For any real C, let L = log₂(6r) and K = |C|/log 2. For r ≥ 1,
L ≥ 1, log₂ L ≥ 0 and log₂ L ≤ L/log 2. Hence
C L log₂ L ≤ K L². The standard limit L²/r → 0 gives
C L log₂ L ≤ r eventually. Changing the exponential base yields

$$
(6r)^{C\log_2\log_2(6r)}\le 2^r\le N.
$$

Choose r to satisfy this threshold and exceed the given dimension cutoff.
The claimed strict count is incompatible with U(6r,N) ≥ 2^N > 2^{N−1}.
The argument accommodates every real C, including nonpositive constants.

## Falsifier

The route requires labelled counting, disjoint quadruples, exact family
cardinality, injectivity of the choice map, and closure under every union.
It also requires the strict tail inequality and a threshold estimate valid
for each fixed real C at arbitrarily large natural dimensions. All these
requirements occur on the live proof path to `result`; a quotient count or
a finite list of dimensions would answer a different question.

## Evidence

The Lean module is `D5/S3/Combinatorics/ErdosUlam/UnionClosedCountRefutation.lean`.
Its named construction lemma is `level_selection_injection`, and its strict
binomial estimate is `binomial_tail_bound`. The final settling declaration
is `result : ¬ claim`. The proof is parameterized by arbitrary natural r and
uses finite-type cardinality theorems and a genuine asymptotic limit, rather
than evaluating any particular value of U. No finite certificate is required.

## Triage

- [proved: Lean `result`] The eventual quasipolynomial counting assertion in
  Question 9.2 is false.
- [proved: Lean `counting_counterexample`] For every r ≥ 4, the explicit
  size N = H + ⌊B/4⌋ satisfies N ≥ 2^r and U(6r,N) ≥ 2^N.
- [proved: Lean `eventual_threshold`] For each real C, every sufficiently
  large r satisfies (6r)^(C log₂ log₂(6r)) ≤ 2^r.
- [open] Determine sharper labelled counting estimates at these or other
  family sizes. The lower bound is not an exact formula for U.
- [open] Resolve the underlying Erdős–Ulam extremal problem or replace this
  failed universal counting route. Proposition 5.4's conditional implication
  is not refuted or formally verified by this module.

## ASSUMED-UNVERIFIED

Forward citations were screened by web search only.
