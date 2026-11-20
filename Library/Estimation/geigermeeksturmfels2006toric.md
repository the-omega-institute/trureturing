---
bibkey: geigermeeksturmfels2006toric
authors: Dan Geiger and Christopher Meek and Bernd Sturmfels
year: 2006
title: On the Toric Algebra of Graphical Models
doi: 10.1214/009053606000000263
url: https://arxiv.org/pdf/math/0608054
claim: "Theorem 4.1 characterizes factorization of strictly positive finite discrete probability distributions by pairwise graphical identities."
strata_touched: [S3]
license: citation-only
triage: anchor
---

# Graphical factorization and pairwise identities

## Verified locator

Geiger, Meek and Sturmfels, *On the Toric Algebra of Graphical Models*,
Annals of Statistics 34(3), 1463–1492,
DOI [10.1214/009053606000000263](https://doi.org/10.1214/009053606000000263).
The [arXiv text](https://arxiv.org/pdf/math/0608054), version 1,
Section 4.2, Theorem 4.1, PDF p. 14, states the Hammersley–Clifford
equivalence for strictly positive distributions in a finite discrete graphical model.

## Scope

The paper's statement concerns probabilities and finite discrete state spaces.
It is background for the relation between nonedge pairwise identities and
clique factorization. It is not a verbatim source for arbitrary dependent
coordinate spaces and arbitrary commutative-group-valued functions.

The algebraic argument in `D5/S3/Combinatorics/Graph/CliqueFactorization/Algebraic.lean`
uses triangular anchored interactions, cancellation, and products over subsets.
Its arbitrary-group and arbitrary-state-space formulation is derived in the
repository. The argument retains the empty-support constant and treats an empty
configuration space separately. No probability normalization or positivity
interpretation is needed for that statement, and no originality claim is made.
