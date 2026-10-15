---
bibkey: beny2010approximate
authors: Cedric Beny and Ognyan Oreshkov
year: 2010
title: General conditions for approximate quantum error correction and near-optimal recovery channels
doi: 10.1103/PhysRevLett.104.120501
url: https://arxiv.org/abs/0907.5391
claim: Approximate error correction and near-optimal recovery can be characterized using a worst-case entanglement-fidelity framework.
strata_touched: []
license: citation-only
triage: anchor
---

# Approximate recovery versus current-region prediction

## Verified source

Cédric Bény and Ognyan Oreshkov, Physical Review Letters 104 (2010), 120501; arXiv:0907.5391. The primary APS and arXiv records were checked.

## Use and boundary

Comparison source for operational recovery criteria. The arithmetic RT quantity inf_C ||N Phi_t - C N||_diamond predicts a future marginal from a present marginal. Its target, feasible maps and norm differ from this paper's static approximate error-correction optimization. No equality between the two tasks is claimed. Exact static recovery of a center algebra can coexist with a nonzero future-prediction deficiency.

## Exact complementary channel criterion

Theorem 1 compares optimal recovery fidelity with an optimization over complementary channels. Taking the target channel to be the identity and the fidelity to be one gives exact recovery on every logical input if and only if the complementary channel is a fixed-state replacement channel. The finite-dimensional identity target has a one-dimensional complementary output. Thus the replacement has the full linear form X ↦ Tr(X) σ, with σ positive and of trace one.

For an isometric encoding with nonzero logical interface, the retained-channel Kraus operators E_a satisfy E_b† E_a = σ_ab I exactly when the complementary output is this replacement. The complete normalized Kraus recovery supplied by the repository acts on the entire retained output algebra, including the orthogonal complement of the code support. Equality only on density inputs extends to all input matrices by positive-cone scaling and complex linear span. The zero-dimensional logical case must be stated separately: absence of logical density inputs does not produce a trace-preserving decoder into the zero matrix algebra.

## Verified locator

- DOI: https://doi.org/10.1103/PhysRevLett.104.120501
- Primary record: https://arxiv.org/abs/0907.5391
- Full text: https://arxiv.org/html/0907.5391v4 , Theorem 1 and its specialization to an identity target channel.
