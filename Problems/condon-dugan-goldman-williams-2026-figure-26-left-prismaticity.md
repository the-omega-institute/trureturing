---
slug: condon-dugan-goldman-williams-2026-figure-26-left-prismaticity
bibkey: condon2026polyominodensity
doi: 10.48550/arXiv.2608.29231
url: https://arxiv.org/abs/2608.29231v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Polyomino/Figure26Prismaticity.left_issue_prismatic
---

# Figure 26 left polyhex prismaticity

## Problem

The caption in Section 9.1, printed p. 33, reads “Two de Bruijn polyhexes
we conjecture are prismatic.” This dossier concerns the left panel, whose
four-cell glyph is the fidget-spinner tetrahex. Its ordered
axial offsets are (0, −1), (0, 0), (1, 0), (−1, 1). The allowed edge
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

Issue [#31892](https://github.com/the-omega-institute/trureturing/issues/31892)
preregisters the exact panel, orientation, quantified minimum, and tier-1
classification. Its bounded check found no earlier exact settlement in
title and polyhex queries, indexed citations, or matching repository
issues, pull requests, and catalog records. The versioned source is v1.

## Route

Choose any 16 distinct anchors of a competing board. The union of their
translates is contained in the board. A nonempty finite set of integer
pairs has no nonzero translation period, so distinct anchors count
distinct translated cell sets.

In the source coordinates, the glyph's central offset is in residue 0 for
r − q modulo 3, and the three arms are in residue 1. The arms in each
input residue are a translated unimodular simplex in the index-three
kernel. If m points expand by g under simplex addition, their occupied
rows and vertical boundary endpoints give 2m ≤ g(g − 1). Output residue
i contains its own centers and the preceding residue's expanded arms.
The 153 nonnegative triples of input counts summing to 16 give a lower
bound of 28 on the sum of the output counts. This final bounded arithmetic
is checked inside the symbolic argument. The issue map sends each source
cell (q,r) to (−q,−r).

The displayed witness attains 28. A spanning-tree certificate verifies
edge connectivity and a finite evaluation verifies the count and the
multiplicities of all 16 words.

## Falsifier

A connected board with at most 27 cells and at least 16 translates of the
specified glyph would refute density. A discrepancy between the panel and
the transcribed cells or fills, or a word with multiplicity different from
one, would invalidate the exhibited witness.

## Evidence

The exact Lean theorem is `D5/S3/Combinatorics/Polyomino/Figure26Prismaticity.left_issue_prismatic`. Its statement
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
