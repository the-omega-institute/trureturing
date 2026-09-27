---
slug: squarefree-mean-partition
bibkey: wiseman2023a360070
doi: null
url: https://oeis.org/A360070
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/SquarefreeMeanPartition.result
---

# Squarefree Numbers Have No Partition Whose Parts and Multiplicities Agree in Mean

## Problem

OEIS A360070, at revision #18 of Jan 29 2023, by Gus Wiseman, Jan 27 2023:

> Numbers for which there exists an integer partition such that the parts have the same mean as the
> multiplicities.

> Conjecture: No term > 1 is squarefree.

The entry's worked example:

> A partition of 20 with the same mean as its multiplicities is (5,4,3,2,1,1,1,1,1,1), so 20 is in
> the sequence.

## Motivation

The frozen theorem `D5/S3/Combinatorics/SquarefreeMeanPartition.result` settles the comment.

## Gap

Issue 9539 records the screen carried out before the work. A360070 appears nowhere under
`Problems/`, `D5/` or `docs/` in this repository. It appears as one `note-only` row in the
2026-09-10 triage record in `Library/Words/`, where the same argument was sketched and the row was
set aside for high bind risk. That disposition is reversed here: the risk named there is about the
proof shape, which is reported as measured, and is not by itself a reason to leave a named external
conjecture unjudged. A web search for a published proof returned only unrelated partition
literature. Citation indices were not exhaustively reachable, so this is a bounded negative finding.

## Route

Present a partition by its set `D` of distinct parts together with a multiplicity function `m`. Let
`M` be the number of parts, the sum of the multiplicities, and `k = |D|` the number of distinct
parts. The mean of the parts is `n / M`, the mean of the multiplicities is `M / k`, so the source's
condition is `n * k = M ^ 2` after clearing denominators. Both denominators are positive for a
partition of a positive number, so nothing is lost and the statement stays inside the naturals. The
worked example is this equation at `M = 10`, `k = 5`: `20 * 5 = 100 = 10 ^ 2`, both means being two.

Suppose `n > 1` is squarefree and such a partition exists.

**One.** `n * k = M ^ 2` gives `n ∣ M ^ 2`; with `n` squarefree this gives `n ∣ M`, say `M = n * j`.

**Two.** Substituting and cancelling the positive `n` leaves `k = n * j ^ 2`.

**Three.** Every multiplicity is at least one, so the number of distinct parts is at most the number
of parts, `k ≤ M`, that is `n * j ^ 2 ≤ n * j`, forcing `j ≤ 1`; and `M ≥ 1` since `D` is nonempty,
so `j = 1` and `M = k = n`.

**Four.** `k = M` with every multiplicity at least one forces every multiplicity to be exactly one.
The total is then the sum of the distinct parts, `n` of them, each at least one. If one of them were
at least two the total would exceed `n`. So every part is one, so `D ⊆ {1}` and `k ≤ 1`,
contradicting `k = n > 1`.

Squarefreeness enters at exactly one place, step one, and that is why the conclusion is about
squarefreeness rather than about `n` being composite.

## Falsifier

The literal sentence fails at `n = 1`: the partition `(1)` has one part and one distinct part, both
means equal to one, and `1` is squarefree; the entry's data has `a(1) = 1`. This is why the comment
says **term > 1** and why the statement carries that bound. The sister entry A360068 carries the
same sentence without the bound and is false as literally written for this reason — a boundary
observation from the definition and the data, not a report of a published refutation.

Reading the mean of the multiplicities as the mean over parts rather than over distinct parts would
give a different equation and a different sequence; the worked example pins the reading.

## Evidence

Enumerating every partition and testing `n * k = M ^ 2` reproduces the entry's data line term by
term up to `n = 60`: `1, 4, 8, 9, 12, 16, 18, 20, 25, 27, 32, 36, 45, 48, 49, 50, 54`. The worked
example checks out as recorded above.

Independently of any partition, the arithmetic alone was swept: for every squarefree `n < 2000`, the
pairs `(M, k)` with `n * k = M ^ 2` and `k ≤ M` were listed, and the only solution is the diagonal
`M = k = n` — exactly the case step four kills. No squarefree `n > 1` appears among the computed
terms.

## Triage

`theorem`; Tier 1 named external open question, preregistered in issue 9539 before the work. The
computational use is `none`: no declaration is a bounded enumeration, a checker, a numeric reduction
or a certified instance, and the delivered statement is universally quantified over every `n` and
every partition.

## ASSUMED-UNVERIFIED

The literature screen is bounded. The entry was read in full at revision #18. Citation indices and
printed sources were not exhaustively reachable, so no worldwide priority claim is made. The weight
is stated plainly: the argument is elementary, and what is settled is that the sentence sat on the
entry unjudged since January 2023.
