---
bibkey: "wolfer2020identity"
authors: "Geoffrey Wolfer; Aryeh Kontorovich"
year: 2020
title: "Minimax Testing of Identity to a Reference Ergodic Markov Chain"
doi: null
url: "https://proceedings.mlr.press/v108/wolfer20a.html"
claim: "First visits to each state provide independent samples from its transition row; the identity tester separately controls failure to obtain the required number of visits."
strata_touched: []
license: "citation-only"
triage: "anchor"
---

# Minimax Testing of Identity to a Reference Ergodic Markov Chain

Proceedings of Machine Learning Research 108, 191–201 (AISTATS 2020).
The publisher page confirms the title, authors, volume and pages.
The inspected full author version is arXiv:1902.00080v3, corrected
24 September 2019, available as [primary HTML](https://arxiv.org/html/1902.00080v3).

Section 6.1.1, within the proof of Theorem 4.1, defines the mapping from
an infinite trajectory to the successors of its first prescribed visits
to a state. The authors credit Daskalakis et al. (2018) for this mapping.
The resulting samples are independent with the specified transition-row
law. Irreducibility makes the infinite-trajectory mapping almost surely
well-defined. A finite trajectory can fail to contain enough visits.
Section 6.1.2 compares the ideal infinite-sample event with the coverage
failure event; it does not infer independence after conditioning on coverage.

First-visit sampling and its finite-horizon coupling are
`literature-attested`. In the parity construction, the extra identities
`P^2 = Pi` and zero outgoing parity mean under the actual reversed kernel
supply a model-specific reduction to biased versus fair independent sign
rows. The sharp sparse direction threshold and the quantitative comparison
of full path and independent-pair experiments require separate
`repo-derived` arguments. The cited identity-testing sample-complexity
bound is not a direction-recovery theorem.
