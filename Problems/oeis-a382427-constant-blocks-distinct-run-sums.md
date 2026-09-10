---
slug: oeis-a382427-constant-blocks-distinct-run-sums
bibkey: oeis2026a382427
doi: null
url: https://oeis.org/A382427
triage: theorem
motivation_gids:
  - D5/S1/Words/Compositions/ConstantBlocksDistinctRunSums
---

# Constant Blocks and Distinct Run Sums

## Problem

OEIS A382427 counts integer partitions of n that can be partitioned into
constant blocks with distinct sums. Its comment conjectures that the same
number counts partitions having a permutation with all distinct run-sums.
A381717, the complement, explicitly conjectures the pointwise equivalence.
Runs are maximal consecutive constant subsequences, as defined by A382876.

## Motivation

This is a first-tier OEIS conjecture by Gus Wiseman, authored March 26, 2025
and created March 28, 2025. The task asks for an unconditional equivalence,
including the empty partition, followed by the partition-count identity.

## Gap

No proof of the target was found in the complete directly referenced OEIS
entries or the searched pinned Mathlib, frozen repository, and public Lean
code results. A381717 still marks its equivalence as Conjecture. This is a
bounded search report, not a claim that no proof exists elsewhere.

A particular distinct-sum decomposition need not admit an ordering with
adjacent values different: three ones split into blocks of lengths 1 and 2
give distinct sums but two blocks of the same value. The source only asks
for existence, so another decomposition may be chosen.

## Route

Choose a valid decomposition with the fewest blocks. If one value has k
blocks and o blocks have other values, assume k > o+1. Add the largest
same-value block sum to each of the other k-1 sums. The candidates are
distinct and exceed every old same-value sum. Since k-1 > o, one candidate
also avoids every other-value sum. Merging that pair preserves all parts
and distinctness of sums but reduces the number of blocks, a contradiction.

Thus each value occurs in at most half the blocks, rounded up. A greedy
induction with a forbidden-first-value invariant constructs an ordering
with adjacent values different. Expanding each block as a constant list
therefore gives precisely the maximal runs. The reverse implication takes
the actual runs as the blocks. The two predicates on Nat.Partition(n) agree,
so filtering its finite universe gives equal cardinalities.

## Falsifier

A positive multiset satisfying exactly one predicate would contradict the
pointwise theorem. An error in the merge argument could appear as a minimal
valid block decomposition violating the count bound. There is no finite
cutoff or additional source hypothesis in the deposited theorem.

## Evidence

The module is `D5/S1/Words/Compositions/ConstantBlocksDistinctRunSums.lean`.
The public results are `constantBlocks_iff_distinctRunSums` and
`card_constantBlocks_eq_distinctRunSums`. Both compile with only propext,
Classical.choice and Quot.sound in their axiom closures. The live new
constructions are `minimal_balanced` and `order_colors`.

Independent worker enumeration compares the two sets of qualifying
partitions for n=0,...,11, and reproduces the OEIS DATA values
1,1,2,3,4,7,11,14,19,28,39,50. The left algorithm splits multiplicities;
the right independently enumerates compositions and extracts maximal runs.
Finite diagnostics are external artifacts, not frozen numerical instances.
The Library note records exact-definition Lean boundary checks and gates.

## Triage

`theorem`: the unbounded pointwise equivalence and counting identity are
proved in Lean. The source conjecture is the formalization target; this
does not assert publication priority. Final freeze and PR receipts belong
to the runner result and Library validation record.

## ASSUMED-UNVERIFIED

No exhaustive literature or Lean-ecosystem search is claimed. The caller's
Section III observation was supplied as ASSUMED-UNVERIFIED and is false for
an arbitrary decomposition, as the three-ones example shows. Its replacement
for a minimum-block decomposition is proved, not assumed. Correspondence
between the source wording and the explicit formal definitions is a
documentary judgment; the Lean kernel proves the stated definitions.
The worker performed implementation and self-checks; no independent review
or first-proof priority is claimed.
