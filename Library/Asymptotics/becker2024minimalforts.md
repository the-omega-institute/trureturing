---
bibkey: becker2024minimalforts
authors: Paul Becker; Thomas R. Cameron; Derek Hanely; Boon Ong; Joseph P. Previte
year: 2024
title: "On the number of minimal forts of a graph"
doi: 10.48550/arXiv.2404.05963
url: https://arxiv.org/abs/2404.05963v1
claim: "Section 6, Conjecture 31: a graph family has a successive minimal-fort-count limit strictly between the cube root of three and two."
strata_touched:
  - D5/S3/Combinatorics/MinimalForts/UniversalRoot
license: citation-only
triage: anchor
---

# Minimal forts and successive growth

Sections 2 and 3 concern finite simple undirected loopless unweighted graphs. A fort is a nonempty vertex subset such that each outside vertex has a number of neighbors in the subset different from one. Section 3 uses the family of all inclusion-minimal forts. Order is the number of vertices.

Section 6, Conjecture 31 asks for a family whose full successive minimal-fort-count ratio has a limit strictly greater than the cube root of three and strictly less than two. The conjecture sentence does not separately impose order n at index n. Connected graphs of every positive order with normalized counts tending to one at base three halves would satisfy a stronger interpretation.

Nguyen Hoang Dat and Franklin H. J. Kenter, arXiv:2605.07298v1, section 5.2, Question 1, explicitly restate Conjecture 31 and report that their attempts to exceed the cube-root-of-three growth rate were unsuccessful. This is a bounded standing observation, not a claim that every subsequent or inaccessible source has been searched. The journal body at DOI 10.1007/s00373-025-02891-z has not been inspected.

The graph construction in `D5/S3/Combinatorics/MinimalForts/EveryOrder.result` uses the universal-root, block-counting and irrational-rotation results to give connected graphs at every positive order. Their complete minimal-fort counts A(n) satisfy A(n)/(3/2)^n tending to one and A(n+1)/A(n) tending to three halves. The count ranges over every actual inclusion-minimal nonempty fort; no graph-count formula is assumed as a hypothesis. This is an existence result, not a determination of the extremal growth rate.

## Verified locator

DOI: 10.48550/arXiv.2404.05963

Primary version: https://arxiv.org/abs/2404.05963v1
