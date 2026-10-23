---
bibkey: benjaminihelmantovzhukovskii2023noisyvoter
authors: I. Benjamini, H. Helman Tov and M. Zhukovskii
year: 2023
title: "Global information from local observations of the noisy voter model on a graph"
doi: 10.1214/23-AOP1637
url: https://arxiv.org/abs/2207.01224
claim: "May Var(ζ₁ + … + ζ_t) be sublinear? We do not have an answer. However, we prove that it is either linear in t or O(ln t)."
strata_touched:
  - D5/S3/StatisticalMechanics/NoisyVoter/RepetitionVarianceLinear
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.1214/23-AOP1637

Source: https://arxiv.org/abs/2207.01224

The source is arXiv:2207.01224v2, *Annals of Probability* 51(5),
1963–1992. Page numbers below refer to the arXiv v2 PDF.

Section 1, p. 2:

> Consider a connected graph G (not necessarily finite) and a real number ε ∈ (0, 1).

> Initially, at time t = 0, all vertices are assigned with independent Bernoulli random variables X₀(u) ∼ Bern(1/2), u ∈ V(G). Then, for every t ∈ ℕ, every u ∈ V(G) (independently of all the other vertices), with probability ε, gets a random opinion Y_t(u) ∼ Bern(1/2), or, with probability 1 − ε, chooses an opinion of one of its neighbors chosen uniformly at random.

Section 2.2, p. 5:

> For every t, consider ζ_t = I(X_t = X_{t+d}).

Section 2.2, p. 6:

> May Var(ζ₁ + … + ζ_t) be sublinear? We do not have an answer. However, we prove that it is either linear in t or O(ln t).

Here ζ_i is the indicator of X_i(u) = X_{i+d}(u), with d ≥ 1.
The unnormalised statistic includes i = 1 through t, including observations
at times i+d beyond t. Equation (7), immediately before the question,
gives an upper bound O(t); Lemma 2.3 gives the linear/logarithmic dichotomy.

The coordinate encoding uses Bool opinions, with true for a refresh.
Each choice takes values in the neighbour subtype and has its uniform law.
Local finiteness and the existence of a neighbour at every vertex make that
law meaningful. The latter excludes the isolated one-vertex graph.

The repository result proves the lower bound
Var(W_t) ≥ (ε^(deg(u)+2)/2)⌊t/(d+1)⌋ and rules out o(t).
Together with the published upper bound this implies Θ(t) variance.
The upper bound and the resulting dichotomy consequence are literature-based
consequences, rather than additional Lean theorems of this module.
This does not imply a central limit theorem or typical √t fluctuations.
The paper's main graph-distinguishability conjecture remains open here.

Prior-art completeness and the corresponding journal typography are
ASSUMED-UNVERIFIED; the quotations and locators use the arXiv v2 text.
