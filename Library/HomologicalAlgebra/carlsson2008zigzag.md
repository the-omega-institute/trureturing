---
bibkey: carlsson2008zigzag
authors: Gunnar Carlsson; Vin de Silva
year: 2008
title: "Zigzag Persistence"
doi: null
url: https://arxiv.org/abs/0812.0197v1
claim: "Proposition 3.11 constructs complementary summands for induced subspaces of filtered vector spaces; the endomorphism remark following Lemma 3.18 gives unique reconstruction from a terminal component preserving the induced filtration; Theorem 3.19 decomposes a finite-dimensional right-streamlined zigzag into terminal intervals with the successive right-filtration quotient multiplicities, ordered by Definition 3.6."
strata_touched:
  - D5/S3/HomologicalAlgebra/FilteredVectorSpaceComplement
  - D5/S3/HomologicalAlgebra/Persistence/ZigzagNaturalLift
  - D5/S3/HomologicalAlgebra/Persistence/ZigzagTerminalIntervals
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

## Terminal interval decomposition

Section 3, Definition 3.6 and Theorem 3.19 in the versioned HTML
https://arxiv.org/html/0812.0197v1 specify the birth ordering and streamlined
interval decomposition. Each forward step appends the new vertex to the birth
ordering; each backward step prepends it. A finite-dimensional right-streamlined
zigzag is isomorphic to a direct sum of intervals ending at its terminal vertex.
The multiplicity at each ordered birth is the dimension of the corresponding
successive quotient of the actual terminal right filtration.

`ZigzagTerminalIntervals.exists_terminal_interval_decomposition` formalizes this
existence statement on the original native actual-arrow path category. It uses
independent field and vertex-space universes, a common explicit ModuleCat lift,
finite occurrences with repeated births, the actual filtration inclusion
quotients, and every active arrow orientation. Finite dimensionality and the
streamlined hypotheses are required only on the active prefix. Paper vertices
1 through m correspond to native vertices 0 through m-1. Native prefix n=0 is
one vertex; the separate zero-vertex empty category and empty sum give the
explicit vacuous extension. Zero spaces and zero multiplicities are included.

The formal statement does not choose canonical summands or a unique natural
isomorphism. It does not strip unrestricted diagrams, allow early deaths, or
assert the full interval classification of Section 4. The construction uses
existing linear complements, sections and finite bases to build compatible
coordinates; it supplies no compatible basis or decomposition as an assumption.
This is literature-attested known-theorem formalization, not a claim of
mathematical novelty.
