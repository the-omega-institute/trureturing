---
bibkey: kimleeyun2025randompermutations
authors: D. Kim; J. Lee; C. Yun
year: 2025
title: "Provable Benefit of Random Permutations over Uniform Sampling in Stochastic Coordinate Descent"
doi: 10.48550/arXiv.2505.23152
url: https://arxiv.org/abs/2505.23152v1
claim: "Assumption 2.2 specifies positive-definite unit-diagonal Hessians; Appendix E.2 displays the exponent-n first-moment comparison as the original matrix AM-GM."
strata_touched:
  - D5/S3/Quantum/Matrix/ProjectionAMGMRefutationScalar200
license: citation-only
triage: anchor
---

# Provable Benefit of Random Permutations over Uniform Sampling in Stochastic Coordinate Descent

The inspected source is arXiv:2505.23152v1. Assumption 2.2, pp.3–4,
specifies real positive-definite unit-diagonal Hessians. Section 4.3, p.9,
states the authors' historical knowledge of general-quadratic RPCD results.
Appendix E.2, pp.50–51, displays the first-moment comparison with exponent
$n$ and calls it the original matrix AM-GM. Its later future-work sentence
concerns a separate second-moment comparison; it is not an explicit statement
that this exact first-moment restriction remained unresolved.

## Verified locator

Inspected arXiv v1: https://arxiv.org/abs/2505.23152v1,
DOI 10.48550/arXiv.2505.23152. The source passages are Assumption 2.2,
pp.3–4; Section 4.3, p.9; and Appendix E.2, pp.50–51. These locators
bind only the inspected arXiv version. Conference-version equality remains
unverified. Appendix E.2's later future-work wording concerns second moments,
not the displayed first-moment comparison.

For ordinary scalar source correspondence, put $C=X^\top X$, take its
symmetric positive-definite square root $S$, and set $U=XS^{-1}$.
Then $U$ is orthogonal and $X=US$; the same orthogonal conjugation carries
every complement projection, each ordered word, their full permutation
average and the mean power. The scalar200 Lean endpoint is the unit-basis
projection assertion itself. No kernel-checked Hessian or update-transport
endpoint is supplied or claimed. KLY does not separately specify the
square-root choice in the inspected passages; this correspondence explicitly
uses the conventional symmetric positive root.

This note reuses the completed source packet, not a new search. Its
37-retrieval and 41/33-row citation screens are incomplete (KLY was absent
from those citation rows); some records were metadata/abstract only and
failed search-engine access supplies no negative evidence. No earlier exact
settlement was located within that scope. Citation completeness and global
absence, priority and novelty remain unverified. Luenberger–Ye fifth-edition
Chapter 14 full text remains unread; the conference version of KLY was not
separately compared. No smallest-dimension, optimal-rate, expected-inverse
or second-moment settlement follows. The source review's architecture
comment and historical proof-shape disagreements remain disclosed in the
existing SLY dossier.
