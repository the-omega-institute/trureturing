---
bibkey: caldwell2024actiongraphs
authors: D. Caldwell, A. Cochran, N. Glisson, B. Jennings, K. McDicken, L. Proctor, S. Klanderman, A. Tebbe
year: 2024
title: Catalan Number Sequences and Generalized Action Graphs
doi: 10.48550/arXiv.2507.22719
url: https://arxiv.org/abs/2507.22719v1
claim: "Conjecture 5.6. The subsequent super Catalan number can be computed from the n-table of its previous action graph via S(0, n + 1) = Σ_{ℓ=0}^{n} (2/2^ℓ) Σ_{v=0}^{n} Kℓ,v,n."
strata_touched:
  - D5/S3/Combinatorics/Graph/SuperCatalanActionGraphRecurrence
license: citation-only
triage: anchor
---

# Super Catalan numbers and generalized action graphs

## Verified locator

DOI: 10.48550/arXiv.2507.22719

Source: https://arxiv.org/abs/2507.22719v1

The journal version is Ball State Undergraduate Mathematics Exchange 18(1),
Fall 2024, pages 88–106:
https://openjournals.bsu.edu/mathexchange/article/view/5831.
The identity is **Conjecture 5** in the journal and **Conjecture 5.6** in arXiv v1.
The journal page is the locator for that version; the arXiv record's journal DOI
10.33043/r2y588ab resolves to an unrelated item and is not used as its locator.

## Source statements

ArXiv v1, page 15:

> Definition 5.1 ([1], A17). The super Catalan numbers are defined by S(m, n) = (2m)!(2n)! / (m!n!(m + n)!).

> Definition 5.2. We construct the sequence generalized action graphs, denoted {Gn}, for the super Catalan numbers as sequence of directed graphs defined inductively in the following way. The graph G0 is a single vertex labeled 0. To construct Gn+1 from Gn, consider each vertex v in Gn. For each 0 ≤ ℓ ≤ n, add p(v, ℓ) · 2/2^ℓ new vertices labeled n + 1 with edges from v, where p(v, ℓ) is the number of paths of length ℓ from v to vertices labeled n in Gn.

ArXiv v1, page 16:

> Definition 5.4. Let Kℓ,v,n be the number of paths of length ℓ in Gn that start at a vertex labeled v and end at a vertex labeled n. For a given n, the table of Kℓ,v,n for all values of ℓ and v is called the n-table.

The example on page 16 gives K₁,₂,₃ = 2×2 + 2×2×2 = 12: all starting
vertices labeled 2 contribute, including the multiplicities in the condensed graph.

ArXiv v1, page 17:

> Conjecture 5.6. The subsequent super Catalan number can be computed from the n-table of its previous action graph via S(0, n + 1) = Σ_{ℓ=0}^{n} (2/2^ℓ) Σ_{v=0}^{n} Kℓ,v,n.

## Encoding and scope

The graphs are rooted trees with edges from parent to child. A list of children
retains every vertex separately. `paths` counts paths from one root, including
the length-zero path; `pathsFrom` accumulates these counts over all starting
vertices with the specified label. Growth uses counts in the old tree. Every
division in the growth rule is exact because 2^ℓ divides each applicable path
count. `S` is the displayed factorial quotient in ℚ. The identity includes n = 0.

## Related results and bounded literature evidence

The preregistration's literature reading at 2026-10-09 found no posted solution
to Conjecture 5.6 at MathDB p/369568. MathDB p/369567 contains a proof of
Conjecture 5.5, the per-label path recurrence, including the integrality argument.
These bounded findings do not assert absence of a prior proof in every source.

Klanderman–McDicken–Tebbe, “Conditions for Building Generalized Action Graphs
From Sequences,” arXiv:2507.22861, PUMP 9 (2026), pages 158–179,
DOI 10.46787/pump.v9i.6304, give a sequence criterion in Theorem 2.1.
Their Section 3.4 says it “answers” the existence question for S(0, n),
with graphs checked through n = 2. This concerns some generalized action graphs;
it does not prove the identity for the particular graphs of Definition 5.2.
