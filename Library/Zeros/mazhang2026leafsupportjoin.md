---
bibkey: mazhang2026leafsupportjoin
authors: "Haobo Ma; Wenlin Zhang"
year: 2026
title: "Alikhani–Griswold, Section 4(3): connected graphs with domination root −4"
doi: "10.5281/zenodo.23919066"
url: "https://doi.org/10.5281/zenodo.23919066"
claim: "Lemma 1: joining leaf supports v_i of graphs H_i along a graph F keeps dominating sets componentwise, so D(J_F,x) = prod_i D(H_i,x), and for r >= 1 J_F is connected when every H_i and F is."
strata_touched:
  - D5/S3/Combinatorics/Graph/Domination/LeafSupportJoin
license: citation-only
triage: anchor
---
<!-- GID: D5/L/Zeros/mazhang2026leafsupportjoin -->
# Leaf-support joining and the domination polynomial product

## Verified locator

The written proof is by **Haobo Ma and Wenlin Zhang**, version 1, exact-version DOI
https://doi.org/10.5281/zenodo.23919066, Lemma 1 in Section 1 of `connected-minus-four/note.tex` in the public source
archive https://zenodo.org/api/records/23919066/files/source-v1.zip/content. The DOI is
10.5281/zenodo.23919066; the concept DOI is 10.5281/zenodo.23919065.

## Statement

Let H_1, …, H_r be vertex-disjoint finite simple graphs with vertices v_i, w_i such that
N(w_i) = {v_i}. For a simple graph F on the indices, J_F adds the edges v_i v_j for ij ∈ E(F).
Restriction and disjoint union are inverse size-preserving bijections between the dominating
sets of J_F and the tuples of dominating sets of the H_i, so D(J_F, x) = ∏ D(H_i, x); the empty
product is 1. If r >= 1 and every H_i and F is connected, J_F is connected.

## Context

The problem and the 33-vertex base graph are due to S. Alikhani and M. Griswold
(arXiv:2608.00109v1, Section 4(3), Theorem 2.1). The added edges are irrelevant edges in the
sense of T. Kotek, J. Preen, F. Simon, P. Tittmann and M. Trinks, *Recurrence relations and
splitting formulas for the domination polynomial*, DOI 10.37236/2475, Definition 3.9 and
Theorem 3.11, whose general irrelevant-edge method is prior work.
