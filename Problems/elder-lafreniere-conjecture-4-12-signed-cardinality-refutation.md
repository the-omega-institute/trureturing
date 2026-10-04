---
slug: elder-lafreniere-conjecture-4-12-signed-cardinality-refutation
bibkey: elder2024toggling
doi: 10.48550/arXiv.2307.08520
url: https://arxiv.org/abs/2307.08520v2
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Geometry/IntervalClosedSignedCardinalityRefutation.result
---

# Signed cardinality is not 0-mesic on [3] × [12]

## Problem

Elder, Lafrenière, McNicholas, Striker and Welch, *Toggling, rowmotion, and
homomesy on interval-closed sets*, arXiv:2307.08520v2, Conjecture 4.12,
states:

> If m = 2 or m = 3, then the signed cardinality statistic is 0-mesic
> under rowmotion on interval-closed sets of [m]×[n] whenever m + n − 1
> is even.

The signed point statistic is 1 on even rank and −1 on odd rank, and the
statistic of an interval-closed set is the sum over its members. The
follow-up by Lafrenière, Lewis, McNicholas, Striker and Welch,
arXiv:2505.04000v1, retains the m = 3 even-n case as an open conjectural
statement in Remark 3.31.

## Motivation

Conjecture 4.12 predicts cancellation of the signed rank statistic on every
interval-closed rowmotion orbit in the stated dimensions. The result gives an
explicit legal orbit in the m = 3 range whose average is −1/73, so the
universal assertion fails while the separately proved two-row result remains
untouched.

## Gap

The target quantifies over every positive n satisfying the parity condition,
every complete reverse linear extension, and every interval-closed initial
set. The unresolved m = 3 clause therefore requires either a proof of
zero sum on all such orbits or one certified nonzero orbit.

## Route

The module reuses the frozen point, reverse-extension, toggle, trace, and
literal-orbit carriers. It defines the rank-parity point weight and its finite
set sum, states the full quantified conjecture, and constructs a row-major
reverse extension of Point 3 12. A natural-number bitmask encodes each
interval-closed state. Lower- and upper-set masks certify order-convexity,
the bit operation agrees with symmetric-difference toggling, and the
73-state cycle is checked transition by transition. Injectivity identifies
the decoded cycle with the distinct literal orbit; the computed signed sum
over that orbit is −1.

## Falsifier

A failure of any of the following would invalidate the refutation: the seed
must be order-convex, the extension must satisfy ReverseExtension, every
toggle transition must agree with the bitmask trace, all 73 transitions must
close the cycle, the decoded states must be distinct, and the signed sum
must be exactly −1. The proof checks each condition in Lean.

## Evidence

The frozen declaration
`D5/S3/Combinatorics/Geometry/IntervalClosedSignedCardinalityRefutation.result`
has type `¬ claim`. Its public definitions are `signedWeight`,
`signedCardinality`, and `claim`, followed by the settling theorem
`result`; the finite masks and transport lemmas are private. The pinned
Lean kernel checks the literal 73-state cycle, its return transition, and the
integer total. The source correspondence is Elder et al.,
arXiv:2307.08520v2, Conjecture 4.12 and Definition 3.17, with the open m = 3
scope attested by Lafrenière et al., arXiv:2505.04000v1, Remark 3.31.
The preregistration is issue [13084](https://github.com/the-omega-institute/trureturing/issues/13084).
The result carries `OpenProblemResolutionClaim(Refuted)`.

## Triage

The named conjecture is refuted for its universal claim; the module is
admitted under `admission_basis: open-problem-resolution` with
`proof_shape: content` and escape witness `result`.

### What the settlement shows

Proved in this module: for m = 3 and n = 12, the row-major reverse extension
and the interval-closed seed {(1,7),(3,2),(3,3),(3,4),(3,5)} produce a
73-state literal orbit whose signed-cardinality sum is −1. This is the
failure mechanism: even rank parity does not force cancellation across a
literal interval-closed rowmotion orbit.

Computed by the kernel-checked certificate in
`D5/S3/Combinatorics/Geometry/IntervalClosedSignedCardinalityRefutation.lean`:
the orbit average is −1/73, hence nonzero. The m = 2 odd-n result proved in
the follow-up and the max-minus-min homomesy theorem in
`D5/S3/Combinatorics/Geometry/RectangleRowmotionHomomesy.result` survive;
they concern different scopes or statistics. Whether any replacement
hypothesis yields signed-cardinality homomesy for the remaining m = 3 cases
is open.

The first three readings below are computed by exhaustive enumeration of
all interval-closed sets of [3] × [n] and their literal rowmotion orbits;
the fourth follows one seed orbit for each listed n:

- Exceptional orbits at n = 12 (computed). IC([3] × [12]) has 47,373
  members in 1,615 rowmotion orbits. Exactly two orbits have a nonzero
  signed-cardinality sum: both have length 73, with sums −1 and +1. The
  poset anti-automorphism (i, j) ↦ (4 − i, 13 − j) maps one onto the other
  and negates every signed weight. The row-major and the rank-major reverse
  extensions give the same orbit decomposition.
- Global cancellation (computed). The sum of the statistic over all of
  IC([3] × [12]) is 0, so the global average still cancels. The conjecture
  fails orbit by orbit, not on average.
- Small cases (computed). For m = 3 the clause m + n − 1 even holds exactly
  at even n. At n = 2, 4, 6, 8, 10 (5, 19, 72, 229 and 661 orbits) every
  orbit has signed-cardinality sum 0. So n = 12 is the first even n at which
  the conjecture fails for m = 3.
- Candidate family n = 8k + 6 (computed; open as a theorem). The seed
  {(1,12), (1,13), (2,6)} is interval-closed in [3] × [n]. Its literal
  orbit has length (n² − 20)/2 and signed-cardinality sum −1 for each of
  n = 14, 22, 30, …, 158 (19 values). No proof covers all k.

The refutation removes Conjecture 4.12 as a valid general premise for later
arguments; results in the source that use the separately proved m = 2
statement retain that scope, while claims relying on the m = 3 even-n
conjecture require revision.

## ASSUMED-UNVERIFIED

The literature check covers the cited arXiv versions and the repository's
registered notes; it does not establish exhaustive worldwide priority or
exclude an unindexed later settlement. The enumeration readings in the
Triage are computed, not kernel-checked; only the n = 12 witness orbit is
kernel-checked.
