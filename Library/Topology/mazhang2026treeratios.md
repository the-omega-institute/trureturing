---
bibkey: mazhang2026treeratios
authors: "Haobo Ma; Wenlin Zhang"
year: 2026
title: "Counterexamples to Conjectures 3 and 4 of Huang, Stoica, Xia and Zhong (arXiv:2006.06716v1, Section 5.2, printed page 32)"
doi: "10.5281/zenodo.23935004"
url: "https://doi.org/10.5281/zenodo.23935004"
claim: "Corollary 5: for a positive solution on a connected locally finite tree with at least one edge, the edge lengths are globally constant if and only if the vertex ratios R_i are globally constant."
strata_touched:
  - D5/S3/Geometry/DiscreteGravity/TreeConstantRatios
license: citation-only
triage: anchor
---
<!-- GID: D5/L/Topology/mazhang2026treeratios -->
# Constant lengths and constant vertex ratios for the tree equations

## Verified locator

DOI: 10.5281/zenodo.23935004

Source: https://doi.org/10.5281/zenodo.23935004

The written proof is by **Haobo Ma and Wenlin Zhang**, *Counterexamples to Conjectures 3 and
4 of Huang, Stoica, Xia and Zhong (arXiv:2006.06716v1, Section 5.2, printed page 32)*, public
version 2 (published 2026-11-04), exact-version DOI https://doi.org/10.5281/zenodo.23935004,
Corollary 5 (label `cor:global` in `note.tex`, section "Extension of the source's line
solutions"). The tree equations of motion are those of A. Huang, B. Stoica, X. Xia and
X. Zhong; see Library note huangstoicaxiazhong2020einstein.

## Statement

> For a positive solution on a connected locally finite tree with at least one edge, the edge
> lengths are globally constant if and only if the vertex ratios $R_i$ are globally constant.

Here c_i is the sum of 1/l_ij and d_i the sum of 1/l_ij^2 over the neighbours j of i,
R_i = c_i/d_i, and the edge equation is (R_i^2 + R_j^2)/l_ij - R_i - R_j = 0. The proof: if
R_i = s everywhere, positivity gives s > 0 and the edge equation gives 2s^2/l_ij - 2s = 0, so
l_ij = s; conversely, if every edge has length s > 0 then c_i = deg(i)/s, d_i = deg(i)/s^2 and
R_i = s. Connectedness and the edge make every degree positive.
