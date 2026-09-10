---
slug: oeis-a068012-subset-sum-doubling
bibkey: oeis2025a068012
doi: null
url: https://oeis.org/A068012
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Parity/SubsetSumModSixDoubling
---

# The A068012 subset sum doubling conjecture

## Problem

Let a(n) count subsets of {1,...,n} whose element sum is zero modulo six.
David A. Corneth conjectured on September 13, 2025 that a(n)=2a(n-1)
whenever n>2 and three does not divide n-1.

## Motivation

This is a first-tier recent OEIS conjecture. Direct inspection on September
8, 2026 found the exact statement still labelled Conjecture. The entry's
finite verification through 2000 is evidence only, not a general proof.

## Gap

The implementation brief reports no independent proof or preprint in its
searched public indexes. The obligation is an identity for all eligible n,
not an extension of the finite verification window.

## Route

Write C(m,r) for the count at residue r modulo six. Splitting at the last
element gives C(n,r)=C(n-1,r)+C(n-1,r-n). Splitting instead at element three
shows C(m,r)=C(m,r+3) for every m at least three.

For m congruent to one modulo three, the total sum m(m+1)/2 is one modulo
three. Complementation maps residue zero to the total-sum residue, which
is either one or four modulo six. The three-periodicity identifies both
with residue one. Thus C(m,0)=C(m,1) for m at least four in that phase.
Taking m=n-1 now gives the doubling identity in each permitted residue
class; the boundary index n=3 is checked inside the general proof.

The brief's group-ring argument for the second lemma yields the same
equality. Projection to modulo three sums the two lifts; three-periodicity
makes this twice either lift, and cancellation of two recovers the result.

## Falsifier

An n>2 with three not dividing n-1 and a(n) different from 2a(n-1) would
contradict the theorem about the defined subset count.

## Evidence

- Module: `D5/S1/Recurrence/Parity/SubsetSumModSixDoubling.lean`.
- Theorem: `subset_sum_mod_six_doubling`.
- Count: powerset of `Finset.Icc 1 n`, filtered by its `ZMod 6` sum.
- Auxiliary results: `count_succ`, `count_three_periodic`, `count_zero_eq_one`.
- There is no finite cutoff in any of the public theorem statements.

## Triage

`theorem`. The exact universal doubling assertion is proved. No converse
or resolution of the entry's other formulas is asserted.

## ASSUMED-UNVERIFIED

First-publication priority is not established. The literature searches do
not exclude private or unindexed proofs. The identification with OEIS is
documentary; the kernel verifies the explicitly defined mathematical count.
