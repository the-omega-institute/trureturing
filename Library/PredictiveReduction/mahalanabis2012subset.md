---
bibkey: mahalanabis2012subset
authors: Satyaki Mahalanabis; Daniel Stefankovic
year: 2012
title: Subset Selection for Gaussian Markov Random Fields
doi: 10.48550/arXiv.1209.5991
url: https://arxiv.org/abs/1209.5991v1
claim: Precision-matrix messages and finite grids provide bounded-treewidth Gaussian variable-selection approximations for mean-square prediction error, with explicit conditioning dependence for general GMRFs.
strata_touched:
  - D5/S3/Quantum/Dynamics/HamiltonianEffectCompletionGenerator
license: citation-only
triage: anchor
---

# Gaussian subset selection and rounded precision messages

The arXiv record gives v1 submitted 26 September 2012. The retrieved PDF has
an internal title date of 9 September 2021; the catalogue year above follows
the arXiv version metadata, not an inferred journal publication.

The parsed primary text was read at Section 1.2, equation (5), Section 1.3,
Section 3.2, Definition 37, Lemma 38 and Theorem 43. Its objective is a trace
of an inverse precision principal submatrix, representing average conditional
mean-square error. Its finite precision grids and message passing are prior
art, including a polynomial dependence on the input condition number. Theorem
43 explicitly does not give an unconditional bit-polynomial FPTAS when that
condition number grows too quickly. Page screenshot requests failed; the
interior locators here are parsed-text checks, not visual page checks.

The unified predictive theory's rounded-Schur chapter instead controls one
half the log determinant of discarded whole modal blocks. Its proof treats
upward rounding as a block-diagonal PSD perturbation of the same selected
matrix, bounds the additive KL increase, and optimizes the resulting finite
message objective. This note does not claim that precision rounding, Schur
messages or dynamic programming are new, or that the cited mean-square-error
theorem already proves the chapter's logdet guarantee.

The existing Lean declaration named in strata_touched concerns commutator
observable completion. It does not prove this paper's algorithms or the
repository's paper-proof optimization results. No priority conclusion or
formal verification is asserted by this literature note.
