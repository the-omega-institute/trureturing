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

## Gap

The complete conjecture is open in this development. Preregistration is
[issue #29912](https://github.com/the-omega-institute/trureturing/issues/29912).
The finite count must first be related to internal words and then bounded
uniformly in both dimension and height. A first-zero path of positive height
has an internal parent whose length is at most `d*(h-1)`.

## Route

For `m=h-1`, let `I_t` count words with nonempty columns and every coordinate
occurring at most `m` times. Transposing a zero-column-allowed incidence matrix
into its labelled rows gives the binomial transform

`(Sum_{r=0..m} binomial(k,r))^d = Sum_{t=0..k} binomial(k,t)*I_t`.

The original optional-letter insertion theorem in
`D5/S1/Words/LatticePaths/MatharA379464Counting` supplies insertion of empty
columns. The desired positive-series identity sums this transform with
geometric weight `2^(-k)`. Parent/append counting must still connect that
internal count to the literal terminal count. Uniform binomial and
exponential-moment estimates then address the diagonal limit.

## Falsifier

A mismatch with the literal first-zero word count invalidates the source
bridge. A counterexample to the uniform estimates invalidates that route.
A finite prefix agreement, fixed-dimension theorem or conditional limit is
not a solution of the conjecture.

## Evidence

The independently recomputed literal recursion, with one branch per nonempty
labelled subset and immediate stopping at zero, gives `a(0..3)=1,1,13,5419`.
These are smoke values, not evidence for the limit. No resolution claim or
external-problem KPI is attached to the supporting work.

## Triage

Tier 1: a recent OEIS conjecture. The target remains the full source assertion.
The finite counting and analytic bridges are supporting obligations; none
alone constitutes a settlement.

### What the settlement would show

Open: the internal-word representation and uniform factorial-scale estimates
would explain why the diagonal root constant is `1/log(2)`. No conclusion is
claimed for neighbouring limits or for source results depending on this
conjecture.

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
