---
bibkey: mazhang2026treeequations
authors: Haobo Ma; Wenlin Zhang
year: 2026
title: "Counterexamples to Conjectures 3 and 4 of Huang, Stoica, Xia and Zhong (arXiv:2006.06716v1, Section 5.2, printed page 32) (version 2)"
doi: 10.5281/zenodo.23935004
url: https://zenodo.org/records/23935004
claim: "Theorem 1: for an integer q >= 2, t > 0 and r > 0 with r != 1, with s_n = t r^n and a = (r^2 + 1)/(r + 1), the infinite (q+1)-regular tree T_q carries a positive nonconstant solution of the tree equations (R_i^2 + R_j^2)/l_ij - R_i - R_j = 0: on a bi-infinite spine the edge v_n v_(n+1) has length a s_n, and at each v_n there are q - 1 attached rooted q-ary trees all of whose edges, including the attachment edge, have length s_n; the vertex ratio R equals s_n at v_n and throughout the branches attached there. Corollary 2: Conjecture 4 of Huang et al. is false, and Conjecture 3 is false on T_q for every q >= 2, even when equal incident lengths are required at every vertex outside a bi-infinite path. Corollary 6: every nonconstant geometric-spine solution has nonconstant tree curvature; with B = q - 1 + (r+1)^2/(r^2+1), an edge inside a branch has K = 4/(q+1) - 2 and its attachment edge has K = 2/B + 2/(q+1) - 2 > 4/(q+1) - 2; for q = r = 2 these are -2/3 and -13/21."
strata_touched:
  - D5/S3/Geometry/DiscreteGravity/GeometricSpineSolutions
license: CC-BY-4.0
triage: anchor
---

# Geometric-spine solutions of the tree equations on every regular tree

## Verified locator

Zenodo record: https://zenodo.org/records/23935004

DOI: 10.5281/zenodo.23935004 (version 2; concept DOI 10.5281/zenodo.23935003). Source PDF:
https://zenodo.org/api/records/23935004/files/note-v2.pdf/content (text extracted locally with
layout preserved, 16,496 characters). Theorem 1 and Corollary 2 are in Section 1; Corollary 6 is
in Section 3.

## Source statement

> For positive edge lengths ℓ_ij = ℓ_ji, put c_i = Σ_{j∼i} ℓ_ij^{-1}, d_i = Σ_{j∼i} ℓ_ij^{-2},
> R_i = c_i/d_i. (1) … E_ij := (R_i² + R_j²)/ℓ_ij − R_i − R_j = 0. (2)

> Theorem 1. Fix an integer q ≥ 2, a scale t > 0 and a real r > 0 with r ≠ 1. There is a positive
> nonconstant solution of (2) on T_q with the following lengths. Set s_n = t r^n (n ∈ Z),
> a = (r² + 1)/(r + 1). (3) Choose a bi-infinite spine (v_n)_{n∈Z}. The edge v_n v_{n+1} has length
> a s_n. At each v_n attach q − 1 disjoint rooted q-ary trees; every edge in these branches,
> including each attachment edge, has length s_n. The ratio R_i equals s_n at v_n and at every
> vertex of a branch attached there.

> Corollary 2. Conjecture 4 of [1] is false. Conjecture 3 is false on T_q for every q ≥ 2, even when
> equal incident lengths are required at every vertex outside a bi-infinite path.

> Corollary 6. Every nonconstant geometric-spine solution of Theorem 1 has nonconstant tree
> curvature. Put B = q − 1 + (r + 1)²/(r² + 1). The curvatures of an edge wholly inside a branch and
> of its attachment edge are respectively K_branch = 4/(q + 1) − 2, K_attach = 2/B + 2/(q + 1) − 2,
> and K_attach > K_branch. In the cubic r = 2 example these values are −2/3 and −13/21.

> Equation (4.10) of [1], printed p. 13, gives K_ij = (2/ℓ_ij²)(1/d_i + 1/d_j) − (R_i + R_j)/ℓ_ij.

## Mathematical scope

The tree T_q is realized on ℤ ⊕ (ℤ × Fin (q − 1) × List (Fin q)): spine vertices n and branch
vertices (n, b, w), a word w in branch b at v_n, joined to its parent. The quantities c_i, d_i,
R_i and E_ij are those of the frozen TreeEquationsNonconstantRefutation module. Formalized for
every q ≥ 2, t > 0 and r > 0: the graph is a tree with every degree q + 1; the lengths are
symmetric and positive and solve (2) on every edge; the spine edges and the ratios are as in
Theorem 1; every incident length at a branch vertex equals s_n; the solution is constant exactly
when r = 1; the two curvature values of Corollary 6 hold, and K_attach > K_branch exactly when
r ≠ 1. The case r = 1 is included rather than excluded.
