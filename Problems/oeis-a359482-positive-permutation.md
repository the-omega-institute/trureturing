---
slug: oeis-a359482-positive-permutation
bibkey: hasler2023a359482
doi: null
url: https://oeis.org/A359482
triage: theorem
motivation_gids:
  - D5/S3/Arith/SumInConcatenation
---

# The permutation question for A359482

## Problem

> Is this sequence a permutation of the integers > 0?

OEIS A359482 defines the lexicographically earliest sequence of distinct
positive terms for which a(n)+a(n+1) is a decimal substring of the
concatenation of a(n) and a(n+1). This dossier concerns exactly the
permutation question. Hasler's July 3, 2023 comment conjectures a negative
answer and, more specifically, that the initial 1 is the only single-digit term.

## Motivation

This Tier 1 OEIS question has a local decimal obstruction that can decide
the unbounded permutation question. The source defines the sequence by
the least-unused rule; the claimed omission must be a theorem about that rule.

## Gap

The implementation seat read the OEIS internal entry and Angelini's blog
F section with Hans/Hasler corrections on 2026-09-10. They give conjectures,
prefixes and programs, but no proof of the single-digit exclusion. The
bounded repository, pinned Mathlib, GitHub Lean-code and arXiv searches in
the source note found no target proof. This does not establish priority.

## Route

For x>0 and 1<=d<=9 the sum has at least as many digits as x. Its occurrence
in the one-digit-longer concatenation is the whole list or one of the two
end positions. The only non-immediate case forces a*10^length(r)=9*value(r);
modulo nine and value(r)<10^length(r) contradict it. Repeated decimal blocks
provide unbounded legal successors, proving that the greedy recursion is
total. Every term after the initial 1 is therefore at least 10, so 2 is missing.

## Falsifier

A positive index with sequence value 2 would refute the missing-value
conclusion. A positive pair (x,d) with d<10 satisfying the specified substring
direction would refute the stronger local obstruction. Legal(1,10),
Legal(10,99), and Legal(99,889) are mandatory positive controls for that direction.

## Evidence

The module D5/S3/Arith/SumInConcatenation.lean proves no_small_successor,
sequence_greedy, sequence_pos, sequence_legal, sequence_tail_ge_ten, and
not_positive_permutation. The three controls were kernel-checked with
decide before the general proof. The original state/used-set recursion and
its least-unused characterization are present in Lean. All public theorems
use only the standard three axioms. Build and freeze receipts are recorded
in docs/reports/a359482-0910.md.

## Triage

theorem. The target is the negative answer to the full permutation question,
obtained by an unbounded proof, with the local one-digit exclusion as its
main ingredient.

## ASSUMED-UNVERIFIED

The OEIS revision history, linked 100000-term file, and A300000 cross-reference
were not opened by this implementation seat. No claim is made about the
stronger conjecture that 10 is the only two-digit multiple of ten. The
identification of the formal rule with the external prose is a source-fidelity
assessment, not a theorem about the web page's bytes.
