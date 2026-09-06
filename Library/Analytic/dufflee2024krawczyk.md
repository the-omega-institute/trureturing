---
bibkey: dufflee2024krawczyk
authors: Timothy Duff and Kisun Lee
year: 2024
title: Certified homotopy tracking using the Krawczyk method
doi: 10.48550/arXiv.2402.07053
claim: Parametric Krawczyk methods certify approximate solution paths of parameter homotopies; exhaustive root or residual-sublevel coverage is an additional obligation.
strata_touched:
  - D5/S3/Quantum/Tomography/CayleyCoverAnalysis
  - D5/S3/Quantum/Tomography/HadamardResidualBarrier
license: citation-only
triage: anchor
---

# Certified parameter homotopies and exhaustive exclusion

Duff and Lee study a parametric Krawczyk method for certifying approximate
solution paths. The arXiv v2 record identifies the paper as accepted for the
Proceedings of ISSAC 2024 and describes a preconditioning strategy, correctness,
and termination results.

The MUB lane shares the use of a preconditioned residual and an interval Jacobian.
It has an extra obligation: every possible common-unbiased vector must be
covered. Certifying paths starting at a known list does not, on its own, prove
that the list exhausts all solutions.

The residual-barrier computation covers the full seed sublevel
`max_a |f_a(u)| <= 2^-18`; the earlier independent pilot used `2^-21`.
For a point of this sublevel the Krawczyk enclosure must include
`C[-epsilon,epsilon]^5`. Dropping this term is valid only at an exact root and
would invalidate sublevel coverage. The library note credits the underlying
verified-numerical framework, not the particular six-dimensional certificate
or its implementation soundness.

The public arXiv abstract and metadata were rechecked on 2026-09-06.
No numbered full-text theorem is used as an unproved Lean axiom.

## Locators

- https://arxiv.org/abs/2402.07053
- https://doi.org/10.48550/arXiv.2402.07053
- Kisun Lee, a priori continuation bounds: https://arxiv.org/abs/2512.01355
- Burr, Hauenstein and Lee, higher-dimensional surface certification:
  https://arxiv.org/abs/2602.07718
