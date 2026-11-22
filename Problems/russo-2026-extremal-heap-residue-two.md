---
slug: russo-2026-extremal-heap-residue-two
bibkey: russo2026extremalheap
doi: 10.48550/arXiv.2611.22780
url: https://arxiv.org/abs/2611.22780v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Permutation/RussoExtremalHeap.result
---

## Problem

Luís M. S. Russo, *Heap-type permutation generation with a prescribed final
arrangement*, arXiv:2611.22780v1, §10 item 1, printed page 20:

> The correctness of the extremal variant is proved for n ≡ 0 (mod 4) and verified by computer for all even n ≤ 10000; a proof for n ≡ 2 (mod 4) (the orbit structure of Zₙ) is open.

[Versioned PDF](https://arxiv.org/pdf/2611.22780v1) · [Preregistration #32907](https://github.com/the-omega-institute/trureturing/issues/32907)

### Statement echo

- For every natural n ≥ 2 with n congruent to 2 modulo 4, the carrier is Fin n,
  and position i represents printed position i + 1.
- Section 3.1 provides the ordered emission rule. The scan of the recorded
  physical swaps starts at the identity. Inverting each state yields the array
  from positions to items. At size two the list is the identity then the
  reversal, connected by the swap of positions 0 and 1.
- At sizes at least six, use Definition 3 through level n−2 and the
  penultimate order 1,…,m,2m,…,m+1 where m = (n−2)/2. Let U be the net of
  this literal penultimate call and T be reversal. Definition 22 prescribes
  the top items by successive powers of Z = U⁻ⁿT at the last position.
  Theorem 18(a) gives the recorded physical partners.
- The literal Z is a single cycle on the full carrier. The powers indexed by
  Fin n list each item once. Every top partner is below the top. The exact
  ordered list covers the full symmetric group without repetition and has
  length n!. At each index the recorded position transposition produces the
  next array. The lists at the top-level boundaries concatenate in recursive
  order. The terminal state is UⁿZ = T. The last emission and final array are
  the reversal, which is lexicographically greatest.

## Motivation

This is the missing unbounded case of Theorem 23(a). The terminal reversal
tests both the source's prescribed schedule and the orbit criterion used to
define it.

## Gap

Theorem 23(b) proves the residue-zero case. Theorem 23(c) reports bounded orbit
checks, including the residue-two case, through 10000. The preregistration
records checked related literature and the author implementation, together
with limits of that screen. Its stated sources establish the finite evidence
and conditional theorem. [Scoped comparison](https://github.com/the-omega-institute/trureturing/issues/32907)

## Route

For n = 4a + 2 and a ≥ 1, put m = 2a. The lower cyclic net and the
penultimate parking cycle compose to give U. Its support has m + 2 points
and forms one even cycle. Since −n is congruent to 2 modulo m + 2, the
literal quotient is U²T. In the order of the U-cycle starting at printed
position n−1, printed position 2 is the next point. Reversal exchanges these
two points. For each other point of the support, reversal goes outside the
support where U is the identity. The next quotient step returns. Thus the
first-return map on the support is the square of the U-cycle after the
transposition of those first two points. That transposition joins the two
alternating cycles. Every off-support point is reached on a two-step return,
so the first-visit relation gives one full orbit. This mechanism covers only
the stated residue-two sizes at least six. The explicit cyclic/classic branch
covers size two.

The preimage of the top position partitions the recursive states. Every
ordered lower call lists its own such fiber and each prescribed parked item
gives a different fiber. The exact list recurrence prepends the prior blocks
in order, then starts the next block at the recorded swap. Theorem 18's net
formula gives UⁿZ = T. Reversal is its own inverse and is the greatest array
by the first differing index.

## Falsifier

An admissible n with a proper orbit of the literal Z, a repeated or missing
array in the prescribed sweep, an invalid recorded transposition, or a
nonreversal terminal array would contradict the corresponding formal clause.
The size-two instance also fixes the exact swap and emitted order.

## Evidence

The settling declaration is
`D5/S3/Combinatorics/Permutation/RussoExtremalHeap.result`.
The supporting module is
`D5/S3/Combinatorics/Permutation/RussoHeapLowerSweep`.
The quotient proof uses the existing
`FiniteEndpointPairing.FirstVisit` and `same_cycle_of_first_visit`.
The literal quotient uses the actual lower execution and integer exponent.
The ordered-state and emitted-array statements use the same physical swaps.

## Triage

Tier 1, theorem. The case is a uniform source-exact resolution under
`open-problem-resolution` for #32907. The settling proof is content, with
`utility: none`. The supporting module supplies the constructive
ordered parking extension and computation of the actual penultimate net
under `escape-witness`.

## ASSUMED-UNVERIFIED

The literature screen is limited to the consulted sources. No broader
priority claim is made. The odd-size question in §10 item 2 and unrestricted
schedule classification in item 3 fall outside the quantified result.
