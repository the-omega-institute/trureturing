---
bibkey: "chanwalther2015aligned"
authors: "Hock Peng Chan; Guenther Walther"
year: 2015
title: "Optimal detection of multi-sample aligned sparse signals"
doi: "10.1214/15-AOS1328"
url: "https://arxiv.org/abs/1510.03659v1"
claim: "Section 3.1 constructs an average likelihood ratio by evaluating component likelihoods at the asymptotic detectable boundary; Theorem 4 proves asymptotic separation with fixed sparsity-exponent slack in the independent Gaussian aligned-signal model."
strata_touched: []
license: "citation-only"
triage: "anchor"
---

# Optimal detection of multi-sample aligned sparse signals

Annals of Statistics 43(5), 1865–1895 (2015). The inspected source is
arXiv:1510.03659v1, a 32-page PDF. Model (2.2), PDF page 3, uses independent
standard Gaussian errors and independent Bernoulli indicators for which
sequences contain an aligned signal interval. Equation (2.4) specifies the
asymptotic ratio of sequence length to signal length.

Section 3.1, PDF page 9, explicitly substitutes the asymptotic detectable
boundary for the unknown mean when forming the component likelihoods;
it then integrates over a sparsity parameter and averages across intervals.
Theorem 4 on that page assumes a mean at its displayed boundary and signal
probability `N^(-beta+epsilon)`, with fixed `0 < beta < 1` and
`0 < epsilon <= beta`. It obtains a statistic diverging in alternative
probability, allowing the sum of Type I and Type II errors to tend to zero.

Evaluating likelihoods at a detection boundary is therefore
`literature-attested`. The theorem does not provide an exact nondegenerate
critical-risk curve, a fixed single-spike prior, a full Markov path, or
uniform control at a bounded-amplitude endpoint. The parity-kernel
adaptation must separately establish the true-law score mean and variance
under the chosen surrogate amplitude, endpoint KL control, and the
necessary and sufficient clipping conditions within its specified rule
family. Those are model-specific `repo-derived` deductions, not a claim
that boundary calibration itself is new.
