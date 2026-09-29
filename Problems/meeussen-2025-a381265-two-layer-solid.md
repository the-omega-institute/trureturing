---
slug: meeussen-2025-a381265-two-layer-solid
bibkey: meeussen2025a381265
doi: null
url: https://oeis.org/A381265
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/TwoLayerSolidPartitions.result
---

# Meeussen's formula for two-layer solid partitions A381265

## Problem

OEIS A381265 counts the solid partitions with two layers whose second layer is
a plane partition of 3. Its COMMENTS line records:

> Conjecture: equal to 3*(2*A000219 -A000990 -2*A000041 +1) tested up to
> n=20.

Issue #10460 fixes the reading. The index `n` is the size of the first layer,
as the data and the example `a(3) = 6` show. Plane partitions are lower sets
of `n` cells of `ℕ³`, and a two-layer solid partition is a pair `P₂ ⊆ P₁` of
them. A000990 counts the plane partitions all of whose cells have row index at
most 1, and A000041 counts `Nat.Partition n`.

## Motivation

The entry (revision 8, 2025-02-18) still marks the formula as a conjecture.
`D5/S3/Combinatorics/TwoLayerSolidPartitions.result` proves it for every `n`.

## Gap

Issue #10460 preregisters the proof route and the literature check. The
entry's history records no proof, and web searches found none.
`not-found-in-searched-scope`.

## Route

1. The plane partitions of 3 are the three lines `{0, e_k, 2e_k}` and the
   three corners `{0, e_i, e_j}`.
2. A plane partition contains the line in direction `k` iff some cell has
   `k`-th coordinate at least 2. Permuting coordinates is a bijection on lower
   sets, so each line lies in `A000219(n) − A000990(n)` of them.
3. It contains the corner `{0, e_i, e_j}` iff it contains `e_i` and `e_j`.
   - Those without `e_i` lie in a coordinate plane. They are the lower sets of
     `n` cells of `ℕ²`, which correspond to the Young diagrams, and hence the
     partitions, of `n`.
   - Those without both `e_i` and `e_j` lie on an axis; there is one for each
     `n`.
   - So each corner lies in `A000219(n) − 2A000041(n) + 1` of them.
4. Summing over the six second layers gives the formula.

## Falsifier

The proof would fail if a plane partition of 3 were missed in step 1, or if
one of the complement counts of steps 2–3 were wrong for some `n`.

## Evidence

Exact enumeration (#10460):
- a lower-set enumeration of `ℕ³` reproduces the data for `n = 3, …, 12`;
- the formula matches there;
- the formula without `+1` fails at every such `n`.

The canonical source is `D5/S3/Combinatorics/TwoLayerSolidPartitions.lean`.
- Public declarations: `planeCount`, `twoRowCount`, `a`, `claim`, and `result`.
- Frozen module statement identity: `sha256:f94dc9bb589e752086c131e993cb3e56fc2f90a5b41c48ac7d2051e91bdf37ce`.
- `result` statement identity: `sha256:05b35cb799c62d876bab6eacf4befbf842a43b6d3e6d922c0bb3f61b49566f84`.
- Freeze event: `sha256:e84fd4f8451f423b6f2584d4e51156ad434825d565c51ee9d17a4efb99b742fb`.
- Project-level frozen prerequisites: `D5/S3/Combinatorics/SolidPartitionFirstColumn` (`IsSolidPartition`) and `D5/S1/Words/Compositions/ZeroPrependedFirstSumsOddParts` (`cellsOfRowLens_card`, `rowLens_sum`).
- The proof uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

## Triage

Tier 1 external named conjecture (OEIS comment line, 2025), preregistered in
issue #10460 before any Lean. `theorem`; resolution `proved`. The public
theorem has `proof_shape: content`: the classification of the plane
partitions of 3, the complement counts and the Young-diagram correspondence
are new propositions on its live path. Admission basis
`open-problem-resolution`; utility `none`.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty,
priority, or the absence of an independent proof.
