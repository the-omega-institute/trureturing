---
bibkey: jiangwenzhong2026alternating
authors: Xinru Jiang, Suzhen Wen, Yueming Zhong
year: 2026
title: "Alternating adjacent-sum polytopes: transfer matrices and Ehrhart series"
doi: null
url: https://arxiv.org/abs/2607.14887v1
claim: "Question Q1 asks for all Gorenstein pairs (s,r) with s ≥ 2 for the alternating adjacent-sum polytope in dimension 2r."
strata_touched:
  - D5/S3/Combinatorics/Geometry/AlternatingAdjacentSumGorenstein
license: citation-only
triage: anchor
---

## Verified locator

DOI: null. Crossref's title query returns no matching record.

Source: https://arxiv.org/abs/2607.14887v1

The version is arXiv:2607.14887v1. Section 1, equation (1), printed p. 2,
defines the polytope. Theorem 1.9 (`thm-gorenstein-s1`) states the even-dimensional
s = 1 Gorenstein property; its proof on printed p. 44 gives the interior-lattice
translation characterization. Proposition 3.21 (`prop-d2-gorenstein`), printed
p. 45, characterizes the dimension-two cases. Corollary 3.24
(`cor-not-gorenstein-all-s`), printed p. 47, gives failure in at least one even
dimension for every s ≥ 2. Section 4, Question Q1 (`q-gorenstein`), printed
p. 48, asks for the complete classification.

## Definitions and question

Section 1, p. 2, reads:

> For integers d ≥ 2 and s ≥ 1, define

$$
\mathcal P_d^{(s)}
=\{x=(x_1,\dots,x_d)\in\mathbb R_{\ge0}^d:
x_i+x_{i+1}\le s+\delta_i,\quad 1\le i\le d-1\},
$$

> where δ_i = 0 for i odd and δ_i = 1 for i even.

The proof of Theorem 1.9, p. 44, states:

> We use the standard interior-lattice-point characterization of Gorenstein lattice polytopes; see, for example, [13, 7].

It proves the identity
`int((n + 3)T₁^r) ∩ ℤ^(2r) = c_r + (nT₁^r ∩ ℤ^(2r))`
for all n ≥ 0. For a positive index q the corresponding characterization is
the existence of an integral c such that
`int((n + q)P) ∩ ℤ^d = c + (nP ∩ ℤ^d)` for every natural n.

Question Q1, §4, p. 48, reads:

> Theorem 1.9, Proposition 3.21, and Corollary 3.24 show that s = 1 yields an infinite Gorenstein family, whereas every s ≥ 2 eventually fails. For s = 3, direct computation (Propositions 3.22 and 3.23) shows that only d = 2 is Gorenstein in even dimensions d ≤ 6; we conjecture this extends to all d ≥ 4. Characterize all (s, r) with s ≥ 2 for which P_{2r}^(s) is Gorenstein.

## Scope of the characterization

The formal statement uses zero-based coordinates in `Fin d`, with capacity
`s + ite((val(i) + 1) % 2 = 0, 1, 0)`. The Gorenstein predicate is exactly the
interior-lattice translation characterization, using ambient real interior
and real set dilation. The classification for s ≥ 2 and r ≥ 1 is precisely
`s = 3 ∧ r = 1`.

The source's s = 1 theorem and its Ehrhart and transfer-matrix identities
are independent of this classification. The computed h*-tables in Remark 3.18
and §3.5 agree with the classification; their numerical entries are not used
in the formal proof. The unimodality and real-rootedness questions in Q2
remain separate.
