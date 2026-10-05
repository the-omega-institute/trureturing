---
bibkey: carlsson2008zigzag
authors: Gunnar Carlsson; Vin de Silva
year: 2008
title: "Zigzag Persistence"
doi: null
url: https://arxiv.org/abs/0812.0197v1
claim: "Proposition 3.11 constructs complementary summands for induced subspaces of filtered vector spaces; the endomorphism remark following Lemma 3.18 gives unique reconstruction from a terminal component preserving the induced filtration."
strata_touched:
  - D5/S3/HomologicalAlgebra/FilteredVectorSpaceComplement
  - D5/S3/HomologicalAlgebra/Persistence/ZigzagNaturalLift
license: citation-only
triage: anchor
---

<!-- GID: D5/L/HomologicalAlgebra/carlsson2008zigzag -->

# Zigzag persistence

Gunnar Carlsson and Vin de Silva, “Zigzag Persistence,” arXiv:0812.0197v1
(2008). The paper develops the representation-theoretic and algorithmic
foundations of persistence for diagrams whose arrows may point in either
direction.

## Verified locator

The checked primary version is https://arxiv.org/abs/0812.0197v1.
Proposition 3.11 and its proof, on PDF pages 13–14, construct a complementary
summand for every induced subspace of a filtered vector space by successively
extending complements inside its increasing layers.

Lemma 3.18 and the endomorphism remark immediately following it are on PDF
pages 16–17.
That remark is the literature source for the terminal-filtration
reconstruction formalized in `ZigzagNaturalLift`.

## Mathematical scope

The paper works over a field with finite-dimensional vector spaces. Its
filtered spaces start at zero, and the complement construction takes place
inside the terminal layer. `FilteredVectorSpaceComplement` proves a broader
statement over any division ring, without a dimension bound or prescribed
chain endpoints: one complement of an arbitrary submodule in the ambient
space splits every layer of a finite increasing chain, including an empty
chain and repeated layers. This is a proved generalization of the recursive
construction, not an attribution of the exact broader statement to the paper.

The theorem in `ZigzagNaturalLift` makes the predecessor reconstruction explicit for a
finite actual oriented path, allows a single vertex with zero edges (`n = 0`) and arbitrary
characteristic, and does not require finite-dimensional vertex spaces. The
note attests the cited reconstruction principle; it does not claim that the
paper states the repository's exact Lean formulation or that the formal
development proves the paper's full interval-classification results.
