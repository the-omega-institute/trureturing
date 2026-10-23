---
bibkey: muellerregensburger2016elementary
authors: Stefan Mueller and Georg Regensburger
year: 2016
title: Elementary vectors and conformal sums in polyhedral geometry and their relevance for metabolic pathway analysis
doi: null
url: https://arxiv.org/abs/1512.00267v2
claim: Every nonzero vector of a subspace cone is a finite conformal sum of support-minimal elementary vectors.
strata_touched: []
license: citation-only
triage: anchor
---

# Elementary vectors of a subspace cone

Theorem 3 in Section 3.1 states that every nonzero vector in an s-cone
is a finite conformal sum of elementary vectors. An s-cone is a linear
subspace intersected with coordinate nonnegativity constraints; its elementary
vectors are the nonzero support-minimal vectors. Lemma 2 gives the support
reduction used in the inductive argument. The paper attributes the linear
subspace antecedent to Rockafellar's Theorem 1.

For a real matrix with finitely many rows and columns, take the subspace to
be its kernel and impose nonnegativity on every coordinate. Theorem 3 then
supplies the nonzero case of conic generation by nonnegative circuits.
The zero vector is the empty conic combination. Replacing coordinate indices
by an arbitrary finite type changes no mathematical hypothesis.

The Lean module `NonnegativeKernelCircuit` proves this finite nonnegative
kernel statement directly and also proves the row-count-plus-one support
bound. The latter uses linear dependence after fixing one positive coordinate.
The paper's bound on the number of summands in a conformal decomposition
is distinct from this bound on each circuit's support.

## Verified locator

- Primary version: https://arxiv.org/abs/1512.00267v2
- Full text: https://arxiv.org/html/1512.00267v2
- Section 3.1, Lemma 2 and Theorem 3.
