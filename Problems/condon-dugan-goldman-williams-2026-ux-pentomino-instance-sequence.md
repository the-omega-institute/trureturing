---
slug: condon-dugan-goldman-williams-2026-ux-pentomino-instance-sequence
bibkey: condon2026polyominodensity
doi: 10.48550/arXiv.2608.29231
url: https://arxiv.org/abs/2608.29231v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Polyomino/LPolyominoSkippedSequence.a
---

# Equality of the U and X pentomino instance sequences

## Problem

Condon, Dugan, Goldman and Williams conjecture that the U and X pentomino instance sequences agree in [*Polyomino Density*, §10, p. 34](https://arxiv.org/pdf/2608.29231v1#page=34). For every positive integer $N$, let $a_{p,N}$ be the least cardinality of a nonempty finite edge-connected subset of $\mathbb Z^2$ containing at least $N$ distinct translates of $p$. The translates may overlap. For

$$
U=\{(0,0),(-1,0),(1,0),(-1,1),(1,1)\},\qquad
X=\{(0,0),(-1,0),(1,0),(0,-1),(0,1)\},
$$

the assertion is $a_{U,N}=a_{X,N}$ for every $N\geq 1$.

## Motivation

Figure 8 gives a column comparison from X boards to U boards. Theorem 6.4 gives the X minimum, making it an exact target for a lower bound on U boards.

## Gap

The X-to-U comparison gives $a_{U,N}\leq a_{X,N}$. The reverse inequality requires controlling the U anchor count on every eligible board, including boards whose rows have gaps.

## Route

For a U board of area $B$ with $A>0$ anchors, bound the contributions from both parities of anchor columns to obtain $A+2\le B$ and $8A\le(B-A-2)^2+4$. An X checkerboard rectangle attains the threshold capacity corresponding to this inequality. Removing a suffix of the final anchor row and its associated outer cells supplies the intermediate thresholds while preserving board connectivity.

## Falsifier

A positive $N$ and a connected U board with at least $N$ anchors and fewer than $N+2+\lceil\sqrt{8N-4}\rceil$ cells would contradict the conjecture by the X formula in Theorem 6.4.

## Evidence

The statement uses the translation-anchor, edge-connectivity and at-least-$N$ minimum definitions in `LPolyominoSkippedSequence`. The source fixes the two orientations, and rotating or translating a shape and its board together preserves the area and the anchor count. The exact conjecture and bounded literature screen are recorded in [issue #31880](https://github.com/the-omega-institute/trureturing/issues/31880).

## Triage

Tier 1 external conjecture. The target quantifies over all positive thresholds and concerns a pair of explicit fixed shapes.

## ASSUMED-UNVERIFIED

Literature outside the bounded screen in issue #31880 remains unverified.
