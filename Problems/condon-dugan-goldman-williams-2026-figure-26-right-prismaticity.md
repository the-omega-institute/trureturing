---
slug: condon-dugan-goldman-williams-2026-figure-26-right-prismaticity
bibkey: condon2026polyominodensity
doi: 10.48550/arXiv.2608.29231
url: https://arxiv.org/abs/2608.29231v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Polyomino/Figure26Prismaticity.right_issue_prismatic
---

# Figure 26 right polyhex prismaticity

## Problem

The caption in Section 9.1, printed p. 33, reads “Two de Bruijn polyhexes
we conjecture are prismatic.” This dossier concerns the right panel, whose
four-cell glyph is the C tetrahex. Its ordered
axial offsets are (0, 0), (1, 0), (−1, 1), (1, 1). The allowed edge
steps are ±(1,0), ±(0,1), and ±(1,−1). The displayed board and its gray
cells are recorded in the formal source and its Blueprint descriptions.

The connected displayed board has 28 cells and contains exactly 16 fixed
translates of the glyph. It realizes each ordered four-bit word exactly
once, with gray represented by true. Every finite nonempty edge-connected
board with at least 16 distinct translates in this fixed orientation has
at least 28 cells. Translates may overlap.

## Motivation

Density and the de Bruijn condition together yield prismaticity for the
displayed board in the paper's hexagonal-lattice sense. The source uses
Figure 26 to exhibit shapes outside the direct polyhex shift construction
from connected square-cell shapes.

## Gap

Issue [#31893](https://github.com/the-omega-institute/trureturing/issues/31893)
preregisters the exact panel, orientation, quantified minimum, and tier-1
classification. Its bounded check found no earlier exact settlement in
title and polyhex queries, indexed citations, or matching repository
issues, pull requests, and catalog records. The versioned source is v1.

## Route

Choose any 16 distinct anchors of a competing board. The union of their
translates is contained in the board. A nonempty finite set of integer
pairs has no nonzero translation period, so distinct anchors count
distinct translated cell sets.

In source coordinates the output column at i is the union of column i
expanded vertically by {0,2} and column i−1 expanded by {0,1}.
The parity argument bounds the interior increase and the first-column
case of equality. A run with excess E ≤ 11 has at most five columns and
at most 47E/33 anchors. Runs separated by a missing input column have
disjoint output supports. Their bounds sum, so total excess at most 11
would allow fewer than 16 anchors. The issue map sends the board by
(q,r) ↦ (−r,−q), and the glyph receives an extra shift of (1,1) with
the opposite shift on every anchor.

The displayed witness attains 28. A spanning-tree certificate verifies
edge connectivity and a finite evaluation verifies the count and the
multiplicities of all 16 words.

## Falsifier

A connected board with at most 27 cells and at least 16 translates of the
specified glyph would refute density. A discrepancy between the panel and
the transcribed cells or fills, or a word with multiplicity different from
one, would invalidate the exhibited witness.

## Evidence

The exact Lean theorem is `D5/S3/Combinatorics/Polyomino/Figure26Prismaticity.right_issue_prismatic`. Its statement
includes both the word multiplicities and the comparison with every eligible
board. The Blueprint gives the ordered offsets, all board cells, and the
gray-cell indicator. The coordinate map preserves edges, cell count,
anchor count, and words. The source locator is
[Figure 26](https://arxiv.org/pdf/2608.29231v1#page=33).

## Triage

Tier 1, `theorem`. The delivery theorem settles the named panel in full.
The proof uses a symbolic lattice bound on arbitrary finite anchor sets
of cardinality 16.

## ASSUMED-UNVERIFIED

The literature search is bounded to the sources recorded in the
preregistration. Unindexed work and a comprehensive scan of citing
literature remain unverified.
