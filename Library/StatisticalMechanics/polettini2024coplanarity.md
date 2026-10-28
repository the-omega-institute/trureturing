---
bibkey: polettini2024coplanarity
authors: Matteo Polettini; Pedro E. Harunari; Sara Dal Cengio; Vivien Lecomte
year: 2024
title: "Coplanarity of rooted spanning-tree vectors"
doi: 10.1007/s11005-025-02026-8
url: https://arxiv.org/abs/2407.16093v1
claim: "The authors conjecture that the 3ⁿ deletion-constriction vectors through n reversible edges span a space of dimension n+1."
strata_touched:
  - D5/S3/StatisticalMechanics/PolettiniPinnedTreeSpanRefutation
license: citation-only
triage: anchor
---

# Coplanarity of rooted spanning-tree vectors

M. Polettini, P. E. Harunari, S. Dal Cengio and V. Lecomte,
*Coplanarity of rooted spanning-tree vectors*, arXiv:2407.16093v1;
Letters in Mathematical Physics (2025).

## Verified locator

DOI: https://doi.org/10.1007/s11005-025-02026-8

Source: https://arxiv.org/abs/2407.16093v1

The arXiv v1 PDF supplies the locators below. The journal full text is not checked.

## Source statements

Page 2, Introduction: “Finally, we conjecture that the 3ⁿ-vectors representing the deletion-constriction through n reversible edges span a n+1 dimensional space.”

Page 6, §2.1: “We assume the graph to be irreducible, that is, there exists a path x ⇝ y of nonzero weight between any two vertices.”

Page 6, §2.1: “In a directed graph, a rooted spanning tree Tₓ with root x is a spanning tree such that each edge is directed along the unique path that leads to the root.”

Page 6, Definition 1: “The conditioned rooted spanning tree polynomial is defined as”

\[
\tau_x^{\setminus A\,\setminus\!\setminus B}
=\sum_{T_x:\ A\cap T_x=\varnothing,\ B\subseteq T_x}r(T_x).
\]

Page 17, Conclusions: “Given the cases n = 1 and n = 2, it is tempting to speculate that the dimension of the linear space spanned by them is n+1. We collected numerical evidence supporting this conjecture in the case n = 3 (in which case the spanning-tree vectors have 27 entries), for graphs up to 13 vertices and randomized values of the weights of the unpinned edges.”

## Mathematical correspondence

The vertices are `Fin N`, and `r x y > 0` specifies the directed edges. A rooted tree
is a parent map that fixes its root, has a positive-rate outgoing edge at every other
vertex, and reaches the root by iteration from every vertex. Its weight is the product
over the non-root vertices. The root loop is auxiliary and is excluded from the product.
Each pin has status `none`, `some true` or `some false`, for neither direction, the
forward direction only or the backward direction only. The sum defining `tau` is the
conditioned polynomial for that status, without rescaling its edge weights.

The universal dimension statement includes nonnegative rates, irreducibility,
distinct reversible pins and irreducibility after deleting the pins. Unit-rate K4
with the triangle pinned satisfies all these hypotheses but has dependent root vectors.

## Experiment reference

The exact finite computation is in
`the-omega-institute/trureturing-experiments`,
`docs/reports/polettini-harunari-dalcengio-lecomte-2024-pinned-cycle-rank/`,
commit `f7b148864def985e33d70c594831b800ba27c22e`.
The `check.py` SHA-256 is
`104a55a023e87413b7aa73a9a40192a7ec445619a06f9bedd0e8f1e1444ea1cd`;
the source preregistration reports `python3 check.py`, exit 0, `RESULT PASS`.

## Literature boundary

Literature completeness is ASSUMED-UNVERIFIED. The source is the pinned arXiv v1;
no general incidence-rank formula is asserted here.
