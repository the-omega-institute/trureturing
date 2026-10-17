---
slug: muney-gilbreath-component-maximum
bibkey: muney2026gilbreath
doi: null
url: https://arxiv.org/html/2606.23721v2
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/FiniteDifferences/GilbreathExtension.result
---

# Finite Gilbreath extension component maximum

## Problem

Leila Muney, *Holes in Valid-Extension Sets of Finite Gilbreath Sequences*,
arXiv:2606.23721v2, Section 16(4), asks:

> Is max_{S∈G_n} #comp(K_S)=2^(n-4) for all n≥5? Verified for n≤10.

The integer triangle is s_a^0=s_a and
s_a^b=|s_(a+1)^(b-1)-s_a^(b-1)| at every valid index. A prefix is Gilbreath
when every positive-row left entry is one. The family G_n consists of every
strictly increasing Gilbreath integer prefix of length n beginning with two and
three.
K_S contains every integer k for which appending k is Gilbreath; no increasing
condition is imposed on this appended integer. Components are literal maximal
runs of common difference two in the finite one-parity extension set.

## Motivation

`D5/S3/Combinatorics/FiniteDifferences/GilbreathExtension.result` gives the
universal upper bound and eligible attainment for every n≥5, together with
finiteness of the full extension set, its single parity and finiteness of its
literal maximal-run set. The statement is exactly `componentMaximum`.

## Gap

The source's Theorem 35 already supplies attainment, while Section 16(4)
asks for the matching universal upper bound beyond the computed lengths.
The bounded literature qualification covers the complete original v2,
official arXiv feeds with one and two records, and complete visible MathDB
searches with twenty and seven results. No exact whole resolution was found
in those scopes. No worldwide absence or priority claim is made.

The distinct maximum-cardinality and uniqueness question, Conjecture 30,
has a posted Shivam Patel proof at MathDB 375513 and is excluded.

## Route

For a nonempty prefix of length at least two, its actual appended triangle
identifies K_S with the preimage of K_(difference S) under
k ↦ |k-last(S)|. This identity includes every integer k. Finite absolute-value
preimages preserve finiteness and a single parity. The literal endpoint-run
bridge enumerates a,a+2,...,a+2m and excludes the adjacent points.

A parity interval has at most two parity intervals in an absolute-value
preimage, with its nonnegative part clipped in the correct parity. Each
maximal-run start in an interval cover must be the left endpoint of one of
its covering intervals; a run start has a unique right endpoint. Thus a cover
by r intervals gives at most r runs.

The actual bottom rows (1,x,y),(1,z),(1) force
(y,z)=(0,0),(2,2),(2,0),(0,2), or (4,2). Their reverse fiber is the even interval
from zero through y+z+2. Consequently every four-entry Gilbreath prefix has a
one-interval full extension set. Applying the exact preimage recursion n-4
times produces a cover by at most 2^(n-4) parity intervals.

For attainment, the source family V_n is used with attribution to
Definition 31 and Theorem 35. Its first entry is two, its entries at positions
2 through n-1 are 2^(i-1)+1, and its last entry is 2^(n-1)-1. Internally it is
indexed by m=n-4 and includes the seed V_4=(2,3,5,7), whose full extension set
is the single run from three through eleven. The difference row of V_(n+1)
is V_n shifted down by one. The full extension set of the m-indexed family
lies between 2m+3 and 2^(m+4)-2m-5. Every extension after shifting down by one
is therefore at least two. Its absolute-value preimage consists of two
separated reflected copies of its maximal runs, so the count doubles at each
step and equals 2^m. Strict increase, the initial entries, exact length and the
Gilbreath property are all proved for this family.

## Falsifier

A valid increasing prefix of any length n≥5 with more than 2^(n-4) literal
maximal step-two runs would refute the upper bound. A failure of eligibility
or of the exact run count in the attributed family would invalidate the
attainment part. The formal statement assumes neither bound nor attainment.

## Evidence

The canonical Lean theorem is `GilbreathExtension.result`; all supporting
triangle, finiteness, parity, interval-cover, base and family proofs are in its
source module. Finite numerical checks are not used as the all-length proof.
The theorem uses ordinary integer and natural arithmetic and no new axiom.

## Triage

Tier 1 explicit recent external closing question, prospectively registered in
issue 17115. Admission basis: `open-problem-resolution`. The whole theorem has
`proof_shape: content`; its live proof uses the new uniform interval-cover
estimate and the unconditional formal reconstruction of the known attaining
family. Bind-only helpers are consumed by these proofs. Attainment earns no
separate open-problem credit. The universal bound and attainment form one
external-question result.

### What the settlement shows

The decisive mechanism is interval-cover doubling from a realizable
four-entry seed, rather than a count of the points in the extension set.
The internal upper-bound lemma applies to every Gilbreath list of length at
least four, without increase or the specified initial pair. This is a
consequence in the same development, not another resolved external question.
The maximum follows from a universal bound and one witness per length; no
finite enumeration of the eligible family is assumed.

## ASSUMED-UNVERIFIED

The bounded literature search establishes no worldwide priority or perpetual
freshness guarantee. Other questions of the source, including the distinct
cardinality and uniqueness question and the prime Gilbreath conjecture, are
outside this result. The source license is an arXiv perpetual non-exclusive
license, not a code license; the Lean and Scribe are independently authored,
and no author program is copied or executed.
