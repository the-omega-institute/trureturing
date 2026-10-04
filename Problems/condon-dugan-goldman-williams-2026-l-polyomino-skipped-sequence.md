---
slug: condon-dugan-goldman-williams-2026-l-polyomino-skipped-sequence
bibkey: condon2026polyominodensity
doi: 10.48550/arXiv.2608.29231
url: https://arxiv.org/abs/2608.29231v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Polyomino/LPolyominoSkippedSequence.result
---

# The L n-omino instance sequence

## Problem

D. M. Condon, E. B. Dugan, L. M. Goldman and E. R. Williams,
*Polyomino Density*, arXiv:2608.29231v1, Section 6.3, p. 28:

> We believe S(5, 1, 2) is the same as the instance sequence for [L pentomino], and we suspect that the instance sequence for the L n-omino is S(n, 1, 2) in general.

The bracketed label represents the inline L pentomino diagram. For every
integer n >= 3, the L n-omino has n-1 left-aligned bottom-row cells and
one top-row cell. Instances are translated copies, as in Section 2.1.
For every N >= 1, its instance minimum is the least cardinality of a
nonempty edge-connected finite board containing at least N instances.
The sequence S(n,1,2) starts at n, then increases by one at position k
if k appears before position k, and by two otherwise.

## Motivation

The source's Theorem 4.9 supplies a closed form for the instance minimum.
Identifying this geometric minimum with the independently specified
self-referential recursion resolves the general suspicion and its
explicitly mentioned pentomino case. The frozen result is
`D5/S3/Combinatorics/Polyomino/LPolyominoSkippedSequence.result`.

## Gap

Issue #12562 preregisters the exact universal statement and a tier-1
classification before the Lean probe. Its bounded literature check covers
the source's v1, Benoit Cloitre's *A study of self-referential sequences*,
arXiv:2506.18103v2, Theorems 5.1-5.3, OEIS A080353, MathDB and the
formal-conjectures corpus. Cloitre describes x=3,4,5, with the algebraic
proof for x=5 omitted; this does not establish the general polyomino
identification. No resolution of the exact general statement was found in
that searched scope. Citing works were not exhaustively audited because
the citation API returned HTTP 429. This is not a priority claim.

## Route

Put d=n-2 and H_d(K)=sum_{0 <= i < K} floor(i/d). For an arbitrary finite
integer-cell board P, give cell (x,y) weight x+d*y. The top and right-most
cells of each L instance share a weight. The other bottom cells give
injective maps into each of the preceding d layers. In an occupied layer,
the maximum-x cell cannot be an instance's top cell. Write s_k for the
layer size, e_k for its top-cell count, and delta_k=s_k-e_k. Then

d*e_k <= sum_{l<k} delta_l.

The cumulative deficits at occupied layers are distinct integers below
D=|P|-I, where I is the instance count. Summing their quotient capacities
gives I <= H_d(D). This argument uses neither connectivity nor compression.

Let K be least with N <= H_d(K+1), and q=N-H_d(K). Retain every
nonnegative cell of weight less than K, and the weight-K cells with
height at most q. This trimmed down-set is edge-connected, contains
exactly N instances, and has N+K+1 cells. The lower bound proves
that the genuine at-least-N minimum is N+K+1.

The identity H_d(K+d)=H_d(K)+K places these minimum values between
successive jump thresholds. It also constructs an earlier index for every
non-jump value. Consequently the increment is two exactly when the index
is missing from the earlier range, and one otherwise. The initial value
is n. Strong induction identifies the minimum with the literal S(n,1,2)
recursion. All these arguments occur inside the proof of `result`.

## Falsifier

A source discrepancy in the L orientation, translation-only convention,
positive sequence indices, edge connectivity, at-least-N condition or
skipped-number recursion would invalidate this interpretation. The formal
claim retains all these conditions. A genuine counterexample to the
universal equality would contradict the kernel-checked result within its
stated definitions and axiom boundary.

## Evidence

- Preregistration: GitHub issue #12562; source arXiv:2608.29231v1,
  Sections 1, 2.1, 4.4 and 6.3.
- Lean source: `D5/S3/Combinatorics/Polyomino/LPolyominoSkippedSequence.lean`.
- Public settling theorem: `result : claim`, with
  `claim = forall n N, 3 <= n -> 1 <= N -> a (L n) N = skip n N`.
- The two sides are independently defined: `a` is the cardinality
  infimum over eligible connected boards; `skip` is the source recursion.
- A connected eligible board is constructed for every n >= 3 and N >= 1;
  the empty-infimum convention is not used by the conclusion.
- Axiom closure: propext, Classical.choice and Quot.sound.

## Triage

`theorem`: Proved, with admission basis `open-problem-resolution` and
utility `none`. Information-escape registration is paused under
CLAUDE.md Section 3.9.

### What the settlement shows

- **Proved in this module:** the universal equality for every n >= 3 and
  N >= 1, by `result`. Its live proof constructs the weighted-layer
  injection, the cumulative-deficit bound I <= H_d(|P|-I), connected
  sharp trimmed down-sets, and the jump-set/missing-set identification.
  These mechanisms are internal proof terms rather than separately
  exported companion theorems.
- **Proved in this module:** the geometric lower bound holds for all
  finite boards, including disconnected boards, and is sharp on connected
  boards. No compression theorem is assumed.
- **Proved by specialization of result:** the believed n=5 case has
  a(L 5,N)=S(5,1,2)(N) for every positive N. The internal minimum formula
  also gives S(5,1,2)(N)=N+1+min{K: N<=sum_{i=0}^K floor(i/3)}.
  Evaluating this cutoff gives the pentomino closed form of the source's
  Theorem 4.9. Comparing that evaluated expression syntactically with
  Cloitre's Theorem 5.3 is not a separately exported formal statement.
- **Computed:** `python3 /tmp/op-lpoly/enum.py 13` enumerates all fixed
  polyominoes through 13 cells. Counts by size are
  1, 2, 6, 19, 63, 216, 760, 2725, 9910, 36446, 135268, 505861,
  1903890. All reachable minima agree with the recursion for n=3,N<=8;
  n=4,N<=6; n=5,N<=5; and n=6,N<=4. These are finite corroborations,
  not the universal proof.
- **Computed:** `python3 /tmp/op-lpoly/relax.py 30` maximizes the
  one-dimensional layer relaxation with total size at most 30. Every
  reachable minimum agrees with the closed form: n=3,N<=22;
  n=4,N<=20; n=5,N<=18. The programs and their earlier readings are
  the numerical material associated with #12562.
- **Proved consequence for the source:** its L instance-minimum formula
  is now identified with S(n,1,2), including the explicitly conjectured
  pentomino case. The source's other density results need no additional
  hypothesis from this identification.
- **Open:** transferring the weighted-layer argument to the P n-ominoes
  appearing alongside L in Theorem 4.9 requires their own layer maps and
  sharp constructions. The equality of their closed forms alone does not
  supply that proof transfer.
- **Open:** the X pentomino sequence question in Section 6.3 and the
  prismatic questions in Section 9 are outside this settlement.

## ASSUMED-UNVERIFIED

Absence of later settlements is bounded by the literature search in
#12562. Unindexed or unpublished work and the rate-limited citing corpus
are not excluded. No publication-priority or exhaustive literature claim
is made. The finite computations do not certify the infinite statement.
