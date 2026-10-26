---
bibkey: jeanseo2022errordetection
authors: Devin C. Jean; Suk J. Seo
year: 2022
title: Optimal Error-detection system for Identifying Codes
doi: 10.48550/arXiv.2208.06052
url: https://arxiv.org/abs/2208.06052v1
claim: Conjecture 1 asserts that every cubic graph has minimum error-detecting identifying-code density at least 3/4.
strata_touched:
  - D5/S3/Combinatorics/Graph/Domination/JeanSeoCubicErrorDetectingCode
license: citation-only
triage: anchor
---

# Optimal Error-detection system for Identifying Codes

## Verified locator

DOI: 10.48550/arXiv.2208.06052

Source: https://arxiv.org/abs/2208.06052v1

The source is arXiv v1. The journal version is *Optimal error-detection system
for identifying codes*, Networks 85(1), 61–75 (2025), DOI 10.1002/net.22254.
Its full text has not been read; its disposition of Conjecture 1 is unverified.

## Source statements

Page 1, Section 1:

> The closed neighborhood of a vertex v ∈ V(G), denoted N[v], is N(v) ∪ {v}.

The same paragraph states “N_S[u] = N[u] ∩ S”.

Page 2, Definition 3:

> If S is a dominating set and u, v ∈ V(G), u and v are k#-distinguished if |N_S[u] − N_S[v]| ≥ k or |N_S[v] − N_S[u]| ≥ k.

Page 3, Theorem 2.1:

> A detector set, S ⊆ V(G), is a DET:IC if and only if each vertex is at least 2-dominated and all pairs are 2#-distinguished.

Page 3: “Note that density is also defined for finite graphs.”

Page 9, Section 4.2.2:

> Conjecture 1. For a cubic graph G, DET:IC%(G) ≥ 3/4.

## Finite counterexample and boundary

The formal counterexample is a simple connected graph on 50 vertices, with
degree three at every vertex. The detector set has 36 vertices. Its density is
36/50 = 18/25 < 3/4. Its closed detector neighborhoods all have at least two
members, and every distinct pair has a directed neighborhood difference of at
least two members. Thus the finite lower bound in v1 is false even with
connectedness imposed. No claim of a minimum code on this graph, an optimal
cubic density, or a uniform proof for the parameterized family is made.

The source's cubic examples at density 3/4 and its Theorem 4.2 family at 7/8
are compatible with this counterexample. A universal cubic lower bound cannot
exceed 18/25. The correct infimum remains open.

## Experiment and literature boundary

The independent finite checker is in the private repository
`the-omega-institute/trureturing-experiments`, commit `90e09a81`, at
`docs/reports/jean-seo-2022-cubic-error-detecting-identifying-code-density/check.py`.
Its SHA-256 is
`5fccbcc0bc2c5ae535386760feae56dfe5a1967b92eebdbdb43bb3e9d8899c67`.
It exits 0 with `RESULT PASS` for parameters 1 through 4. The output SHA-256 is
`3818494ce3170c73f304c596cf950c875d2c029b2e1777ba606625a375ea2f70`.
These computed cases do not establish a uniform theorem.

The literature screen recorded in issue #19618 inspected later preprints
2504.14124, 2307.16312, 2306.12583, 2212.08193, 2211.14962, 2209.04500 and
citing paper 2407.10595, and found no settlement in that scope. Completeness is
ASSUMED-UNVERIFIED, especially for the unread journal revision. A prior
resolution would remove open-problem credit without changing the finite
counterexample.
