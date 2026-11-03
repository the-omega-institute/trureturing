---
bibkey: koljancicoblak2026nssp
authors: Sara Koljančić; Polona Oblak
year: 2026
title: Combinatorial aspects of the nonsymmetric strong spectral property for graphs
doi: 10.13001/ela.2026.10523
url: https://arxiv.org/abs/2604.21552v1
claim: "Problem 1.8 asks whether the minimum number of arcs in an n-vertex digraph requiring nSSP is 2n-1."
strata_touched:
  - D5/S3/Combinatorics/SpectralGraph/KoljancicOblakMinimumArcs
license: citation-only
triage: anchor
---

# Non-symmetric strong spectral property

The journal version is Electronic Journal of Linear Algebra 42, 755–779,
DOI 10.13001/ela.2026.10523. Problem 1.8 is on printed page 759 and
Theorem 5.5 is on page 771. The arXiv version is 2604.21552v1.

Definition 1.1 says that a real matrix A has nSSP when
A ∘ X = 0 and AXᵀ − XᵀA = 0 imply X = 0 for every real X.
Definition 1.3 says that a digraph requires nSSP when every real matrix
having exactly its directed support has nSSP. Loops are allowed; arcs
are ordered pairs without multiplicity. There is no additional diagonal,
trace, sign or eigenvalue condition.

Problem 1.8 asks: “Is the minimum number of arcs in a directed graph G
on n vertices that requires the nSSP equal to 2n−1?” The positive-order
interpretation includes n = 1. Theorem 5.5 supplies the double path with
an endpoint loop, for arbitrary real nonzero weights. Remark 2.10(1)
identifies its 2n−1 arcs. This upper construction is prior art.

The arXiv version is licensed CC BY-SA 4.0, as stated at
https://arxiv.org/html/2604.21552v1. No article-specific publisher license
is assigned here. The quotations and source definitions above are attributed
to Koljančić and Oblak; this note retains no publisher PDF or source archive.

The bounded literature qualification in issue #25108 located the question in
both versions and found no resolution in its inspected readings. Exhaustive
nonresolution and priority are not established.

The centralizer dimension argument uses the classical structure theorem for
finitely generated torsion modules over K[X], a principal ideal domain.
The actual supplier is pinned Mathlib's Module.equiv_directSum_of_isTorsion,
with Module.AEval.isTorsion_of_finiteDimensional. Coordinatewise multiplication
on the resulting product of cyclic quotient rings embeds injectively in the
original operator's centralizer. This argument works over the original field.

## Verified locator

- Journal: https://doi.org/10.13001/ela.2026.10523, Electronic Journal of
  Linear Algebra 42, 755–779; Problem 1.8 on printed page 759 and
  Theorem 5.5 on page 771.
- Versioned preprint: https://arxiv.org/abs/2604.21552v1; Definitions 1.1
  and 1.3, Problem 1.8, Theorem 5.5 and Remark 2.10(1).
- HTML text and CC BY-SA 4.0 statement:
  https://arxiv.org/html/2604.21552v1.
