---
slug: meeussen-2004-solid-partition-first-column-tau4
bibkey: meeussen2004a098052
doi: null
url: https://oeis.org/A098052
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/SolidPartitionFirstColumn.result
---

# The first columns of A098052 and A098530

## Problem

OEIS A098052 (Wouter Meeussen, 2004) counts the solid partitions of `n` by
their number of extensions:

> T(n,k) counts the solid partitions of n that can be extended to a solid
> partition of n+1 in exactly (k+3) ways. Equivalently, the number of solid
> partitions of n that have exactly k+3 partitions of n+1 majoring them.

and its COMMENTS state

> First column is conjectured to be A007426 = tau_4(n).

The twin entry A098530 (Meeussen, 2004) counts the solid partitions of `n + 1`
by the number of solid partitions of `n` they just cover and states

> First column conjectured to be the (beheaded) A007426.

A007426 is `tau_4(n)`, the number of ordered factorizations `n = rstu`.
Issue #10330 fixes the readings: a solid partition of `n` is read through its
four-dimensional Ferrers diagram, a lower set of `n` cells of `ℕ⁴` in the
coordinatewise order; an extension of `I` is a solid partition of `n + 1`
containing `I`, and a shrinking of `J` is a solid partition of `n` contained in
`J`. The statement settled is that for every `n ≥ 1` exactly `tau_4(n)` solid
partitions of `n` have four extensions and exactly `tau_4(n + 1)` solid
partitions of `n + 1` have one shrinking.

## Motivation

Solid partitions are the four-dimensional analogue of plane partitions. They
are the random variables of Nekrasov's "Magnificent Four" model
(arXiv:1712.08128), the equivariant count of D0-branes in a D8-anti-D8
system, and the charge functions studied for such models (for example
arXiv:2512.24343) detect exactly the cells that can be added to or removed
from a partition. The frozen declaration
`D5/S3/Combinatorics/SolidPartitionFirstColumn.result` shows that the solid
partitions with the fewest possible extensions, and those with a single
shrinking, are exactly the boxes, which proves both conjectures.

## Gap

Issue #10330 preregisters the statement and its literature check. A098052
(last modified 2025-02-03) and A098530 (last modified 2012-03-30) still state
the first columns as conjectures. OEIS full-text searches for `A098052`,
`A098530` and `solid partitions extended` return only these entries and
A007426. The three-dimensional analogue A098529 asserts that its first column
is A007425 without proof. The web searches of #10330 found no statement of
the four-dimensional counts. These readings are
`not-found-in-searched-scope`; they do not establish an exhaustive worldwide
literature search or priority, and the two-dimensional case (a Young diagram
with exactly two addable cells is a rectangle) is standard.

## Route

For positive `v` let `box v` be the set of cells `c` with `c_i < v_i` for all
`i`.

1. `box v` is a lower set with `∏ v_i` cells, and it determines `v`; so the
   boxes of `n` cells correspond to the ordered factorizations of `n`.
2. Every extension of `box v` adds one of the four axis cells `v_i e_i`: all
   cells strictly below the added cell lie in the box, so it has one nonzero
   coordinate `i`, equal to `v_i`.
3. A nonempty lower set `I` that is not a box has at least five extensions.
   With `v_i` one more than the largest `i`-th coordinate in `I`, the four axis
   cells `v_i e_i` can be added, and so can the cell of least coordinate sum in
   `box v` outside `I`, which is not an axis cell.
4. The only solid partition of `n` inside a box of `n + 1` cells is the box
   without its top cell. A lower set `J` that is not a box has two cells with
   nothing of `J` strictly above them: the cell `m` of largest coordinate sum,
   and, above a cell of `J` not below `m`, the cell of largest coordinate sum;
   removing either one leaves a solid partition of `n`. If every cell of `J` is
   below `m`, then `J` is the box of `m + 1`.

## Falsifier

A solid partition that is not a box with at most four extensions, or with a
single shrinking, would refute the statement; steps 3 and 4 exclude both.

## Evidence

A direct enumeration of the lower sets of `ℕ⁴`, grown cell by cell, reproduces
A000293 for `n = 1, …, 11` (`1, 4, 10, …, 3122, 6500`). For each of these `n`
the least number of extensions is 4, and the numbers of solid partitions with
exactly four extensions and with exactly one shrinking both equal `tau_4(n)`;
`tau_3(n)` differs at every `n ≥ 2`.

The canonical source is `D5/S3/Combinatorics/SolidPartitionFirstColumn.lean`.
Its public declarations are `IsSolidPartition`, `extensions`, `shrinkings`,
`a098052FirstColumn`, `a098530FirstColumn`, `tau4`, `claim`, and `result`. The
frozen module state has statement identity
`sha256:90b801db654f0a88c5b3cc511ec61df422b0c7a56ee9b3e26bc19f0631e1cdbe`.
The result declaration has statement identity
`sha256:7b75193af7f63fa373cc5dd373fb23dfdb8e4e0202f313afe74e0e5f82db5424`.
The Freeze event is
`sha256:39bbea1235ade706624c6c1793c186cda4f6aa15fc3aef803f52f22bc66bda9e`
and has no project-level frozen prerequisites. The proof uses only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`,
`native_decide`, or new axiom.

## Triage

`theorem`; resolution `proved`, for both first-column conjectures as read in
#10330. The public theorem has `proof_shape: content`: the characterizations
of the lower sets with four extensions and with one shrinking as boxes are new
propositions on the live path of the proof and are not instances of pinned
lemmas. `admission_basis: open-problem-resolution` under preregistration issue
#10330. There is no atom and no digestion coverage edge. The result is a
uniform theorem for every `n`, so `utility: none` applies.

## ASSUMED-UNVERIFIED

The two conjecture lines are unsigned; attributing them to the entries' author
is an assumption. Reading solid partitions as four-dimensional Ferrers
diagrams, and "extended … by adding 1 element" as containment in a solid
partition of `n + 1`, follows the entries' own "Equivalently" sentences. The
bounded literature check does not establish exhaustive worldwide novelty,
priority, or the absence of an independent proof.
