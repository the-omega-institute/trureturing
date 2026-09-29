---
bibkey: "narang2026stars"
authors: "Ijay Narang; Will Perkins; Timothy L. H. Wee"
year: 2026
title: "Optimal detection of planted stars via a random energy model"
doi: "10.48550/arXiv.2602.15585"
url: "https://arxiv.org/abs/2602.15585v1"
claim: "Theorem 1.1 states a Gaussian total-variation window for detecting a planted star with one uniform hidden hub, and Corollary 1.8 states the corresponding hub-recovery probability."
strata_touched: []
license: "citation-only"
triage: "anchor"
---

# Optimal detection of planted stars via a random energy model

The inspected source is arXiv:2602.15585v1, submitted 17 February 2026,
34 pages. Theorem 1.1, page 3, considers a star of size `k` planted around
a single uniform hidden hub in a graph with `n` vertices and `m` edges.
Under `(log n)^2 << k << sqrt(n)` and
`m = k^2 n / (4 log n) * (1 + gamma / sqrt(log n))`, it states
`TV(P_1,P_0) = 1 - Phi(gamma/sqrt(2)) + o(1)`.
Corollary 1.8, page 5, states the same limiting hub-recovery probability.
These are close prior statements about a Gaussian window and one hidden
location, so those general mechanisms are not claimed as new here.

This version contains a statement inconsistency: Remark 1.6 says that the
null likelihood concentrates at one half throughout that entire window,
using Proposition 1.5(ii). Since
`TV(P_1,P_0) = 1 - E_0 min(1,L)`, convergence `L -> 1/2` in null
probability would instead force the total variation to tend to one half
throughout the window. This conflicts with the varying limit in Theorem
1.1 away from `gamma = 0`. The note records the statements as published;
it does not resolve which assertion requires correction.

The paper is cited as related literature, not used as a proof premise.
The parity-kernel theorem concerns known amplitude and one fixed unknown
spike, two orientations, independent pairs or a full Markov path, and
uniform control as amplitude approaches either endpoint. Its double-tilt
moment bounds and overlap calculation are proved separately as
`repo-derived` deductions. No equivalence with the planted-star experiment
or global originality is asserted.
