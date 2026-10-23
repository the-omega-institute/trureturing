---
bibkey: giuffrida2025descriptionlength
authors: F. Giuffrida, T. Squartini, P. Grünwald and D. Garlaschelli
year: 2025
title: Description length of canonical and microcanonical models
doi: 10.1103/1sd2-rxmy
url: https://arxiv.org/abs/2307.05645v4
claim: "Section IV.C asks whether model-level equivalence implies measure-level ensemble equivalence, the converse of implication (71)."
strata_touched:
  - D5/S3/Divergence/ModelLevelEnsembleEquivalenceConverseRefutation
license: citation-only
triage: anchor
---

# Description length and ensemble equivalence

The source is arXiv:2307.05645v4, published in Physical Review Research 7,
043057. Page numbers below refer to this arXiv version.

## Verified locator

DOI: 10.1103/1sd2-rxmy

Source: https://arxiv.org/abs/2307.05645v4

## Source statements

Section III, p. 4: “Specifically, we will focus on discrete data that can be
represented as a binary n × m matrix G, i.e.” Equation (12) then specifies
the row and column indices. On p. 4: “Ω(c) denotes the number of configurations with c(G) = c, i.e.,”
precedes (15). Section III.A, p. 4: “When considering microcanonical models, entropy maximization yields the following functional form”
precedes (16), the uniform law on the selected fiber. “Its maximum log-likelihood simply reads”
precedes (17), whose exponential is the reciprocal fiber size.
Section III.B, p. 4: “When considering canonical models, entropy maximization yields the following well-known exponential form”
precedes (20), the normalized exponential canonical law. Its expectation-matching condition is (21):
“The ML estimators θ̂(G) are found by solving the system of equations”.

Section III.B, p. 5: “The maximum log-likelihood of a canonical model is linked to the microcanonical one through the Kullback-Leibler divergence:”
precedes (22), which defines the divergence specialized to matched parameters in (23).
Section II, p. 3: “with θ̂(x) being the maximum-likelihood (ML) estimator of θ, i.e.”
precedes (5). On the same page: “The unique solution to this minimax problem reads”
precedes (8), followed by “which is a normalized maximum likelihood.”
Equation (8) divides each maximized likelihood by its sum over data.
Section IV.C, p. 9: “Inspired by the measure level definition of non-equivalence [18] of equation (35), we consider the following KL divergence”
precedes (69), which defines
the model divergence as the finite Kullback–Leibler divergence between the
two normalized maximum-likelihood laws.

Section IV.C, p. 9: “Following the standard definition and assuming that
the more relevant scale to consider is still the system size n, we say
that the canonical and microcanonical models are equivalent on the
model level if” followed by equation (70), the limit of model divergence
divided by n being zero.

Section IV.C, p. 9, following (71): “i.e., whenever ensemble equivalence
holds, the corresponding microcanonical and canonical models are
equivalent on the model level. The reverse implication, verified here
in the specific case of one-sided local constraints, will be
investigated in future work.”

## Mathematical scope

The scalar case on binary square matrices is sufficient to test the
general converse. The observed matrix sequence is restricted to one for
which a finite real expectation-matching parameter exists eventually.
The canonical likelihood uses a supremum, including boundary limits for
extreme statistic values. The normalization scale remains n, rather than
the number n² of matrix entries.

The counterexample statistic uses the first column, with zero-based
coefficient 1 + 2^(−i−1). Its equal-sized fibers make the microcanonical
normalized maximum-likelihood law uniform. A rank bound controls the
canonical normalization, whereas balanced first columns have exponentially
small canonical probability. These statements concern this scalar
family; they do not change the source's results for one-sided local
constraints.

Literature-search completeness and the thesis screen recorded in issue
#18580 are ASSUMED-UNVERIFIED.
