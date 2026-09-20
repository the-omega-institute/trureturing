---
bibkey: giraldi2018projection
authors: Loic Giraldi; Olivier P. Le Maitre; Ibrahim Hoteit; Omar M. Knio
year: 2018
title: Optimal projection of observations in a Bayesian setting
doi: 10.1016/j.csda.2018.03.002
url: https://arxiv.org/abs/1709.06606v3
claim: Gaussian observation projection can be optimized for posterior KL, expected posterior KL, or mutual information; these objectives differ from selecting dynamically invariant state modes.
strata_touched:
  - D5/S3/Quantum/Dynamics/HamiltonianEffectCompletionGenerator
license: citation-only
triage: anchor
---

# Information objectives and the object being compressed

L. Giraldi, O. P. Le Maitre, I. Hoteit, O. M. Knio, Computational Statistics & Data Analysis 124 (2018), 252–276. The retained Section 14 source reading checked the arXiv v3 metadata, authors' institutional records, and parsed full text at Sections 3.1–3.3. A requested page screenshot failed; no figure or table interpretation is used here.

The paper forms reduced observations by a linear projection and compares the resulting posterior or mutual information with the full experiment. Section 14 of docs/develop/theory/SYMPLECTIC_PREDICTIVE_COMPLETION.md instead retains a subset of whole state modes, keeps their exact posterior marginal, and reconstructs discarded modes with the prior. Its objective is an average recovery KL. The shared Gaussian identities do not identify these two optimization problems.

The source establishes substantial prior art for information-based Bayesian dimension reduction. It does not by itself establish the repository section's nonresonant dynamical constraint, cardinality minimization of a principal precision determinant, or forest approximation bound.

The existing commutator-completion Lean declaration is a mathematical interface for invariant observables. Its Scribe note acknowledges this statistical literature as context only. No paper statement or new optimization theorem is assigned a fictitious Lean handle or machine-proof status.
