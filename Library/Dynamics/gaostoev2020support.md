---
bibkey: "gaostoev2020support"
authors: "Zheng Gao; Stilian Stoev"
year: 2020
title: "Fundamental limits of exact support recovery in high dimensions"
doi: "10.3150/20-BEJ1197"
url: "https://arxiv.org/abs/1811.05124v4"
claim: "Exact support recovery in additive sparse-signal models is related to maxima and minima; the paper gives first-order recovery boundaries under broad dependence conditions and independent-coordinate likelihood-ranking Bayes results."
strata_touched: []
license: "citation-only"
triage: "anchor"
---

# Fundamental limits of exact support recovery in high dimensions

The inspected primary manuscript is arXiv:1811.05124v4, 15 April 2019,
42 pages. The published work appeared in *Bernoulli* in 2020 with the DOI
above. The source models observations as a sparse additive signal plus noise;
its sparsity parameter and amplitude parameter must not be identified with
this repository's parameters merely because their letters coincide.

Theorem 2.1, printed p. 7, gives an upper recovery boundary for asymptotically
generalized Gaussian marginal tails. It allows arbitrary dependence in the
upper bound. Theorem 4.1, p. 19, proves probability-one failure below the
boundary for thresholding procedures when maxima and minima are uniformly
relatively stable. Its class includes thresholds depending on the observations.
This is a statement about exact set recovery, not a conclusion inferred from
divergence of expected Hamming loss.

Theorem 3.1, pp. 13–14, characterizes uniform relative stability for Gaussian
triangular arrays through uniform decreasing dependence. The discussion on
p. 14 distinguishes this first-order property from a Gumbel distributional
limit and displays the familiar Gaussian logarithmic correction. It explicitly
explains why finer distributional convergence requires stronger information
than relative stability. Therefore first-order thresholds alone do not supply
a critical-window risk curve.

Section 5 supplies Bayes lower-bound arguments beyond thresholding. In
particular, Proposition 5.1 and Theorem 5.1, p. 23, concern independent
coordinates with log-concave densities. Lemma 5.3, pp. 23–24, discusses
likelihood-ratio ranking for independent coordinates with a common signal
density. The present parity analysis uses its own complete-data likelihood,
fixed-cardinality posterior and explicit randomization at discrete ties.
No independence or continuous-score assumption is transferred to a Markov
trajectory from these source statements.

The extreme-value viewpoint and likelihood-ranking principles are
`literature-attested`. The source does not directly instantiate the parity
model's observation-dependent compound-Poisson row laws, compensated
background, common-law fixed-row comparison, or full-data minimax reduction.
The second-order parity recovery curve in
[PARITY_HIDDEN_ARROW](../../docs/develop/theory/PARITY_HIDDEN_ARROW.md)
requires those additional arguments. This attribution is not a claim that a
worldwide search has established originality of the general method or of every
possible equivalent formulation.
