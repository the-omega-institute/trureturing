---
bibkey: filimonovapuzynina2026abelianperiodicity
authors: Arina Filimonova; Svetlana Puzynina
year: 2026
title: "On abelian periodicity of purely morphic words"
doi: null
url: https://arxiv.org/abs/2605.30306v1
claim: "Section 4 asks for an upper bound on the iteration K in the primitive binary rank-one criterion for abelian periodicity."
strata_touched:
  - D5/S1/Words/RankOneMorphismIterationBound
license: citation-only
triage: anchor
---

# Abelian periodicity of purely morphic words

Arina Filimonova and Svetlana Puzynina, *On abelian periodicity of purely
morphic words*, arXiv:2605.30306v1 (28 May 2026),
<https://arxiv.org/abs/2605.30306v1>.

The paper's Theorem 1 gives a criterion for the primitive binary rank-one
branch (the source notation has `theta₂ = 0`).  For a prolongable morphism,
the fixed word is abelian periodic exactly when an iterate admits a split
`f^K(a)=uv`, `f^K(b)=u'v'` whose two cyclic rotations have abelian-equivalent
period blocks.  The source asks in Section 4 whether the iteration variable
`K` has an upper bound making this criterion algorithmic.  The source's
abelian periodicity permits an arbitrary finite preperiod.

The formalization keeps the actual binary images, exact Parikh vectors, the
four-word cyclic witness, and arbitrary preperiods.  It proves the explicit
bound `K ≤ 2^(|f(a)|+|f(b)|)` for every nonerasing prolongable primitive
rank-one morphism and supplies an executable finite checker with the same
semantics.  The bound is an iteration bound; it is not an incidence-matrix
bound and does not restrict to pure periodicity.

## Verified locator

URL: https://arxiv.org/abs/2605.30306v1

Locator: arXiv v1, 28 May 2026, Section 4.  The open question is:
“is there an upper bound on M from Theorem 1 making our criterion
algorithmic?”  The Lean source uses `K` for this iteration variable.

The bounded preregistration and ownership screen is recorded in GitHub issue
[#13429](https://github.com/the-omega-institute/trureturing/issues/13429).
That screen is a bounded repository and indexed-literature search, not a
worldwide priority claim.
