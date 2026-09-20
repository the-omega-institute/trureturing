---
bibkey: spantini2017goaloriented
authors: Alessio Spantini; Tiangang Cui; Karen Willcox; Luis Tenorio; Youssef Marzouk
year: 2017
title: Goal-Oriented Optimal Approximations of Bayesian Linear Inverse Problems
doi: 10.1137/16M1082123
url: https://arxiv.org/abs/1607.01881
claim: Low-rank Gaussian posterior approximations can be optimized for a specified quantity of interest and a specified statistical loss; this does not by itself impose autonomous reduced dynamics.
strata_touched:
  - D5/S3/Quantum/Dynamics/HamiltonianEffectCompletionGenerator
license: citation-only
triage: anchor
---

# Goal-oriented Bayesian reduction

## Verified source and scope

SIAM Journal on Scientific Computing 39(5), S167–S196 (2017).
The parsed arXiv text was inspected at Section 2.3, equations (2.22)–(2.26), and Theorem 2.9. The approximation is a low-rank linear function of the data, and the Bayes squared-error loss is weighted by the quantity-of-interest posterior precision. The earlier covariance approximation uses a Riemannian matrix discrepancy.

## Use in the unified theory

Section 13 of `docs/develop/theory/SYMPLECTIC_PREDICTIVE_COMPLETION.md` uses this as prior art for statistically targeted reduction. Its own model instead fixes thermal-coordinate Euclidean energy loss and requires an invariant state subspace. Those are different optimization problems. Spectral low-rank optimality alone is not claimed as new.

The Scribe association is contextual. The existing Lean commutator-closure declaration does not certify the new Bayesian optimization proof.

## Verification boundary

The PDF parser returned the cited equations. Repeated page-screenshot calls returned service errors, so no visual page or figure verification is claimed. This is a citation note, not a reproduction of the article or a global priority determination.
