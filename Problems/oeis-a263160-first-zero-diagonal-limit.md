---
slug: oeis-a263160-first-zero-diagonal-limit
bibkey: kotesovec2026a263160
doi: null
url: https://oeis.org/A263160
triage: theorem
motivation_gids:
  - D5/S1/Words/LatticePaths/KotesovecA263160
---

# First-zero lattice paths and the A263160 diagonal limit

## Problem

OEIS A263160 revision 21 defines `a(n)=A263159(n,n)` and quotes:

> Conjecture: Limit_{n->oo} a(n)^(1/n^2)/n = 1/log(2). - Vaclav Kotesovec, Nov 09 2026

A263159 revision 16 counts finite ordered paths from `(h,...,h)` in `d`
labelled coordinates. A step decrements a nonempty subset by one. The path
stops at the first zero in any coordinate. Simultaneous first zeros give one
terminal word. Zero dimension or zero height gives the immediate empty path,
count one. The logarithm is natural and the exponent is a real power.
The target is the limit along every natural index, with no fixed-dimension
hypothesis or subsequence restriction.

## Motivation

The number of coordinates grows together with the initial height. Thus a
fixed-dimension endpoint asymptotic does not answer this question. The stopping
rule also differs from ending with all coordinates zero: a coordinate may
reach zero while the others remain positive.

## Formal result

`D5.S1.Words.LatticePaths.KotesovecA263160.diagonal_limit` proves

```lean
Tendsto (fun n : ℕ => Real.rpow (a n : ℝ) (1 / (n : ℝ)^2) / (n : ℝ))
  atTop (nhds (1 / Real.log 2))
```

Here `a n = paths n n`; `paths` counts the literal finite first-zero words,
not a series chosen to have the desired limit. The finite range is exhaustive
by `first_zero_length_bound`. The proof only discards the cofinite indices
below two. It makes no fixed-dimension or subsequence assumption.

Preregistration is [issue #29912](https://github.com/the-omega-institute/trureturing/issues/29912).
The result is not frozen or delivered to dev. Independent source/proof-shape
review, canonical settlement, final required checks and delivery remain unpaid.
The source-bound audit is unfinished under
[issue #29924](https://github.com/the-omega-institute/trureturing/issues/29924).
No resolved-problem KPI is claimed.

## Counting bridge

For `m=h-1`, let `I_t` count words of nonempty labelled coordinate subsets
in which every coordinate occurs at most `m` times. Such a word has length
at most `d*m`. Put `I = Sum_{t=0..d*m} I_t`.

Appending any of the `2^d-1` nonempty steps to an internal word either stays
internal or reaches its first zero. These outcomes are disjoint and exhaustive.
A simultaneous first zero remains one word. Every nonempty internal word has
one parent; the empty internal word is unique. Summing the append partition
therefore proves, for `d>0`,

`paths(d,m+1) = 1 + (2^d-2)*I`.

For `P_m(k) = Sum_{r=0..m} binomial(k,r)`, transposing an incidence matrix
with optional empty columns into its independent labelled rows gives

`P_m(k)^d = Sum_{t=0..k} binomial(k,t)*I_t`.

The original generic optional-letter insertion theorem in
`D5/S1/Words/LatticePaths/MatharA379464Counting` supplies insertion of empty
columns. Its original `count` and `insertion_formula` declarations are exposed
in place with their proofs preserved. The shifted geometric binomial identity
from pinned Mathlib then yields the convergent positive sum

`Sum_{k>=0} 2^(-k)*P_m(k)^d = 2*I`.

## Uniform estimates

Vandermonde's identity and the standard binomial factorial bounds give

`(k+1-m)_+^m/m! <= P_m(k) <= (k+m)^m/m!`.

All parameters remain free. With `N=m*d`, every positive-series term is a
lower bound for `2*I`, while the sum-integral/Gamma upper estimate gives

`2*I <= 2^(m+1)*N! / ((log 2)^(N+1)*(m!)^d)`.

The upper comparison uses a monotone polynomial and an antitone exponential
as separate factors; their product is not assumed globally antitone. For the
lower bound choose `k = ceil(N/log 2)+m`. Taking logarithms and using the
public Mathlib factorial-log estimates gives

`N*log(N/log 2)-N-(m+1)*log 2-d*log(m!) <= log(2*I)`

and

`log(2*I) <= (m+1)*log 2+log(N!)-(N+1)*log(log 2)-d*log(m!)`.

The terminal-count relation transfers these estimates to the source count.
For every `n>=2`, the compiled quantitative estimate is

`abs(log(a(n))-n^2*(log(n)-log(log 2)))`

`<= n*(4*log(n)+6+2*abs(log(log 2)))`.

Division by `n^2`, the limit `log(n)/n -> 0`, and continuity of the exponential
prove the exact real-root limit. Positivity follows from the finite count;
the conversion to `Real.rpow` does not introduce an extra hypothesis.

## Falsifier

A mismatch with the literal first-zero word count invalidates the source
bridge. A counterexample to the uniform estimates invalidates that route.
A finite prefix agreement, fixed-dimension theorem or conditional limit is
not a solution of the conjecture.

## Evidence

The independently recomputed literal recursion, with one branch per nonempty
labelled subset and immediate stopping at zero, gives `a(0..3)=1,1,13,5419`.
These are smoke values, not evidence for the limit. The limit is carried by
the Lean theorem and its axiom closure; no external-problem KPI is attached
before independent review and actual dev delivery.

## Triage

Tier 1: the full source assertion is the formal theorem. Repository settlement
and delivery remain separate from the proof.

### What the settlement would show

The internal-word representation and uniform factorial-scale estimates
identify the diagonal root constant `1/log(2)`. No neighbouring limit or
fixed-dimension endpoint formula is added as a separate deliverable.

## ASSUMED-UNVERIFIED

Worldwide priority and completeness of the literature search remain
unverified. The OEIS source still labels the limit a conjecture. Crossref's
exact A263160 query returned no records and GitHub's Lean identifier searches
returned no target in their searched scope. Google returned a challenge and
Bing returned irrelevant results, so neither supports an absence claim.
The full bodies of GHOW1990, DOI 10.1007/BF01787724, and Caughman2011,
DOI 10.1016/j.disc.2011.04.024, are not verified here. Pemantle-Wilson
math/0512548 section 4.9 is a fixed-dimension endpoint-alignment supplier,
not the required source correspondence and uniform diagonal theorem.
