---
bibkey: "pilanci2020neural"
authors: "Mert Pilanci; Tolga Ergen"
year: 2020
title: "Neural Networks are Convex Regularizers: Exact Polynomial-time Convex Optimization Formulations for Two-layer Networks"
doi: null
claim: "Two-layer ReLU weight-decay optimization admits an exact convex formulation using activation-pattern cones, with optimal-value equivalence and reconstruction at sufficient width."
strata_touched: []
license: "citation-only"
triage: "anchor"
url: "https://arxiv.org/abs/2002.10553"
---

# Neural Networks are Convex Regularizers

## Verified locator

ICML 2020; arXiv:2002.10553v2, Section 3, equation (8), Theorem 1 and Remark 3.2. The formulation enumerates diagonal activation patterns and retains the inequalities `(2D-I)Xv >= 0` and `(2D-I)Xw >= 0`. Theorem 1 equates optimal values of the convex program and the weight-decay neural-network problem for `m >= m*`, and reconstructs a network optimizer. The polynomial complexity statement fixes data rank (or input dimension); it is not a polynomial bound uniform in arbitrary rank.

The sign-cone constraints are relevant to the actual-image restriction of patternwise summaries. Static optimum equivalence does not establish equality of synchronous gradient-descent trajectories, and PSD/rank conditions on a Gram matrix do not replace these sign constraints.
