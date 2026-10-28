---
bibkey: mynhardtroux2021irredundance
authors: C. M. Mynhardt; A. Roux
year: 2021
title: "Irredundance Graphs"
doi: null
url: https://arxiv.org/abs/1812.03382v3
claim: "A dominating set is minimal dominating if and only if it is irredundant; every selected vertex then has a closed-private neighbour."
strata_touched:
  - D5/S3/Combinatorics/Graph/Domination/TrapezohedralMinimalDomination
license: citation-only
triage: anchor
---

# Minimal domination and closed-private neighbours

Section 1.1 defines a D-private neighbour of a selected vertex v as a vertex dominated by v but by no vertex of D minus {v}. Its private neighbourhood is PN(v,D) = N[v] minus N[D minus {v}]. In particular, a vertex isolated in the induced graph G[D] is its own private neighbour. A set is irredundant when every selected vertex has a private neighbour.

Observation 1.1(ii) states: “A dominating set is minimal dominating if and only if it is irredundant.” The surrounding text attributes these classical facts to Propositions 3.8 and 3.9 of its reference [16]; Mynhardt and Roux is the verified source used here, not a claim of original authorship of the characterization.

The repository's independently proved `minimalDominating_iff_private` retains the same closed-private convention and all-proper-subset minimality, with no finiteness assumption on the vertex type. No novelty is claimed for this general formulation. The graph-specific fixed-tag correspondence and subsequent counting derivations are repository results, rather than statements attributed to this paper.

## Verified locator

- URL: https://arxiv.org/abs/1812.03382v3
- Full text: https://arxiv.org/html/1812.03382v3
- Section 1.1, definitions of minimal domination, private neighbourhood and irredundance; Observation 1.1(ii).
