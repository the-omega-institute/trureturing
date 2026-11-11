---
bibkey: eilenbergmaclane1954groupsii
authors: Samuel Eilenberg and Saunders Mac Lane
year: 1954
title: "On the Groups H(Π, n), II: Methods of Computation"
doi: 10.2307/1969702
url: https://www.jstor.org/stable/1969702
claim: Theorem 2.1a gives the normalized product-chain Alexander–Whitney and shuffle identities and their recursive chain homotopy.
strata_touched: []
license: citation-only
triage: anchor
---

# On the groups H(Π,n), II

Samuel Eilenberg and Saunders Mac Lane, *On the Groups H(Π, n), II: Methods of Computation*,
Annals of Mathematics, second series, **60** (1954), 49–139.
Theorem 2.1a is on printed page 51. The primary PDF has SHA-256
`bd03c0601b608be67d680bef0ac352a51e0494bb9ad4fd38b8419b6b773ee1ab`.
The theorem's normalized product-chain convention is the quotient by
degeneracies. It is not the abstract Moore-kernel convention used in the
bisimplicial software source described in `li2026bisimplicialeilenbergzilber`.
No additional quotient-to-kernel comparison is supplied here.

The software's formal integer operator family retains the recursive
Eilenberg–Mac Lane construction, with `phiOp(0)=0` and
`phiOp(q+1)=-(phiOp(q)).prime+(hOp(q+1)).prime.comp(D0op(q+1))`.
Here `M₂.comp M₁` applies `M₁` first. The error
`(phiOp q).comp(boundaryOp q)+(boundaryOp(q+1)).comp(phiOp(q+1))
 + idOp(q+1)-hOp(q+1)` is a structural norm for every natural `q`.
Moore retraction kills its realization. The resulting normalized homotopy
has boundary `AW-then-shuffle - identity`. These statements describe the
formal source's conventions and do not import unproved side identities,
naturality or coherence assertions from a different formulation.

No paper text or scan is reproduced here.

## Verified locator

- DOI: https://doi.org/10.2307/1969702
- Publisher record: https://www.jstor.org/stable/1969702
