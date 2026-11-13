---
slug: chen-lin-2026-question-6-1-flip-threshold-limit
bibkey: chenlin2026directionflips
doi: 10.48550/arXiv.2609.14655
url: https://arxiv.org/abs/2609.14655v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.source_fullConvergence
---

# The strict direction-flip threshold has a limit

## Problem

Hao Chen and Yupeng Lin, *Oriented Paths with Few Direction Flips Are
Tournament Anti-Sidorenko*, arXiv:2609.14655v1, Question 6.1, p.19:

> Does the limit of $\frac{f(k)}{k}$ exist as $k \to \infty$?

The definition on p.2 is:

> For an integer $k\ge1$, let $f(k)$ denote the maximal
> $m\in\{0,1,\ldots,k\}$ such that every orientation of the $k$-edge
> path with fewer than $m$ direction flips is tournament anti-Sidorenko.

An orientation is an arbitrary sign vector $x\in\{-1,1\}^k$ on vertices
$0,\ldots,k$. A positive sign directs the corresponding edge forward;
a negative sign directs it backward. A flip is an internal index at
which the adjacent signs are unequal, equivalently their product is $-1$.
For a finite nonempty loopless tournament $T$, define

$$t(P,T)=\frac{|\{\phi:V(P)\to V(T):\phi\text{ preserves every arc}\}|}
{|V(T)|^{k+1}}.$$

All maps are counted, including noninjective maps. The path is TAS when
$t(P,T)\le2^{-k}$ for every such $T$. Thus the exact assertion is

$$\exists L\in\mathbb R\;\forall\varepsilon>0\;\exists K\in\mathbb N,
\quad K\ge1\quad\text{and}\quad
\forall k\ge K,\quad\left|\frac{f(k)}k-L\right|<\varepsilon.$$

The limit ranges over all positive lengths and every placement of signs.
No numerical limit value or restriction on the tournament hosts is part
of Question 6.1. The value at length zero is outside the assertion.

## Motivation

The endpoint is
`D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.source_fullConvergence`.
It proves `SourceFullConvergence` without additional hypotheses.
The source note is `D5/L/Asymptotics/chenlin2026directionflips`.
Existence makes the asymptotic flip threshold a single real quantity;
determining that quantity is the separate Problem 6.2 in the source.

## Gap

The complete existence assertion is proved. The numerical value of the
limit and the exact lower limit requested in Problem 6.2 are not
determined by these theorems. No finite certificate, regular-host
assumption, uniform bound on a witnessing host or subsequence conclusion
replaces the stated assertion.

## Route

For a sign word $w$ and a host of order $N$, give each arc weight $2/N$.
Let $B$ be the product of the forward or transposed arc matrices selected
by the signs, and let $\operatorname{mass}(B)$ be the sum of its entries
divided by $N$. Counting all path assignments gives

$$\operatorname{mass}(B)=2^{|w|}t(P_w,T).$$

A non-TAS word of positive length $k$ with $r$ flips therefore has an
actual finite host with mass $q>1$. That host has $N\ge2$. Reverse the
word and complement every sign to obtain its reflection. Concatenating
the word and its reflection has transfer $BB^{\mathsf T}$, length $2k$
and at most $2r+1$ flips. Positive semidefinite Cauchy–Schwarz gives
log-convex moments. Induction on these moments proves

$$\operatorname{mass}((BB^{\mathsf T})^m)\ge q^{2m}
\qquad(m\in\mathbb N).$$

The two one-edge extension masses sum to $2(N-1)/N$ times the current
mass. At each step at least one sign retains the factor
$c=(N-1)/N\in(0,1)$. Recursively selecting signs gives a tail of every
length $s$ retaining at least $c^s$ of the mass, within the same host.

For every length $n=2km+s$, with $0\le s<2k$, repeat the reflected pair
$m$ times and append such a selected tail. Its mass is at least
$c^{2k}q^{2m}$, which exceeds one for all sufficiently large $m$.
Its flip count is at most $2m(r+1)+s$. Consequently, for every $\delta>0$,

$$\frac{f(n)}n<\frac{r+1}k+\delta$$

holds for every sufficiently large $n$, rather than only multiples of
$2k$. All constructions and inequalities use the same witnessing host.

Let $L$ be the infimum of $\{1\}$ together with the ratios $(r+1)/k$
of all positive-length non-TAS words. This set is nonempty and bounded
below by zero. If $f(n)<n$, maximality supplies a non-TAS word with
exactly $f(n)$ flips; hence $L\le(f(n)+1)/n$. The saturated case
$f(n)=n$ also gives $f(n)/n\ge L-1/n$. Approximating the infimum from
above and applying the propagation inequality gives the matching
eventual upper bound. Thus $f(n)/n$ converges to $L$.

## Falsifier

The literal negation would assert that for every real $L$ there is an
$\varepsilon>0$ such that for every natural $K\ge1$ there is a $k\ge K$
with $|f(k)/k-L|\ge\varepsilon$. A counterexample must use the exact
maximum, strict flip comparison and all-map TAS definition above.
A calculation at finitely many lengths cannot establish this negation.

## Evidence

All Lean names below have prefix
`D5.S3.Combinatorics.ExtremalDensity.ChenLinFlipLimit`.

| Source clause | Formal correspondence |
| --- | --- |
| Every integer sign vector and every flip placement | `Sign` and the bijection `signVectors` |
| Adjacent signs have product $-1$ | `sourceFlips`, `sourceFlips_eq` |
| All arc-preserving maps and denominator $|V(T)|^{k+1}$ | `SourceArcPreserving`, `sourceDensity`, `sourceDensity_eq` |
| Every finite nonempty loopless tournament | `SourceTAS`, `tas_arbitrary_host`, `sourceTAS_iff` |
| The maximum over $0,\ldots,k$ with strictly fewer flips | `sourceThresholds`, `sourceThresholds_eq`, `sourceF_eq_f` |
| Real epsilon/K convergence at every positive length | `SourceFullConvergence`, `source_fullConvergence` |

The decisive counting identity is `mass_transfer_eq_density`, using
the induction `row_transfer_count`. The growth argument uses
`logconvex_geometric_lower`, `moment_geometric_lower`,
`mass_power_geometric` and `reflected_power_amplification`.
The recursive construction `exists_padding` yields `tournament_padding`;
`defect_propagation` combines amplification and padding, and
`fullConvergence` applies the infimum criterion.
The axiom closure of both convergence endpoints is
`{Classical.choice, Quot.sound, propext}`.

The immutable mathematical event is
[issue 28569, comment 6749493942](https://github.com/the-omega-institute/trureturing/issues/28569#issuecomment-6749493942).
Its complete event paragraph has 1,342 UTF-8 bytes without a trailing
newline and SHA-256
`2b5ebf2f8c814ded695e1dded5c93c7e3276614c7e8f909640abe0ebeca9ddf8`.
The original v1 PDF has SHA-256
`cda2fae8cfedda699b0dba7acfd54ec88f2c5b786507fec9d7a4975643a90b62`;
the source archive and TeX identities are given in the Library note.
The source is cited for its question and definitions; its manuscript
and source archive are not redistributed here. No experimental program
or data is a premise of the proof.

The source-owner Reg mirror has a validated four-slot registration for
`logconvex_geometric_lower`. The other 24 public theorem audits remain
unfinished under [issue 28591](https://github.com/the-omega-institute/trureturing/issues/28591)
and the CLAUDE §3.9 linked-issue exception. This is not full registration
coverage, and an unknown continuation is not an undecidability result.

## Triage

- **PROVED.** Question 6.1: the exact strict flip-threshold ratio has a
  real limit over all positive lengths, by `source_fullConvergence`.
- **PROVED.** A finite non-TAS word propagates to every sufficiently
  large length with limiting upper threshold $(r+1)/k$, by
  `defect_propagation`. The same finite host supports the construction.
- **PROVED.** Padding exists for each remainder length, by
  `tournament_padding`. The appended signs are selected; this does not
  state the corresponding inequality for an arbitrary prescribed tail.
- **COMPUTED.** No numerical limit value or finite search certificate is
  asserted. The result uses unbounded mathematical estimates.
- **OPEN within this formalization.** The numerical value in Problem 6.2
  and quantitative host-uniform convergence bounds remain undetermined.
  They are not additional resolved problems.

## ASSUMED-UNVERIFIED

The bounded source and literature screen attached to the mathematical
event found no complete supplier of the assertion. This does not verify
unindexed or unpublished literature, exhaustive citation coverage or
worldwide priority. No novelty or priority claim follows from the
formal result. The formal correspondence and axiom closure do not by
themselves establish literature completeness.
