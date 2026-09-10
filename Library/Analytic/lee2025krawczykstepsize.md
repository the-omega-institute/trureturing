---
bibkey: lee2025krawczykstepsize
authors: Kisun Lee
year: 2025
title: A priori bounds for certified Krawczyk homotopy tracking
doi: 10.48550/arXiv.2512.01355
claim: A priori step-size bounds control certified Krawczyk continuation for affine-linear parameter homotopies; nonlinear MUB residual parameterizations require their own perturbation estimates.
strata_touched:
  - D5/S3/Quantum/Tomography/CayleyCoverAnalysis
  - D5/S3/Quantum/Tomography/HadamardResidualBarrier
license: citation-only
triage: anchor
---

# Step-size budgets for continuation

The paper develops explicit a priori step-size bounds and an iteration-count
analysis. Theorem 2 in the inspected v1 HTML is stated for an affine-linear
parameter homotopy, with a tightened certificate at the current parameter and a
looser target certificate over the next step. Its budget depends on the
preconditioned parameter forcing and its Jacobian.

This informs the use of separate local contraction, root-migration, and global
residual budgets in the MUB lane. It cannot be applied merely because the MUB
parameters move along a straight line. The squared-modulus residual depends
nonlinearly on the complex matrix entries, and the Hadamard matrix itself can
depend algebraically on the seed parameters.

The current lane avoids that unsupported substitution by proving directly
`|normSq(z)-6| <= tau + rho(5+rho)` when `|normSq(w)-6| <= tau <= 1/4` and
`norm(z-w) <= rho`. Columnwise matrix bounds supply the required rho uniformly
for every unit-entry vector. This transfers an entire approximate-root set to
a fixed seed sublevel without tracking individual roots.

The formal source does not import the paper as an axiom. Its real/complex norm
inequalities use Mathlib. The interval evaluator and exhaustive traversal still
require a separate kernel soundness bridge.

## Locators

- https://arxiv.org/abs/2512.01355
- https://arxiv.org/html/2512.01355v1
- https://doi.org/10.48550/arXiv.2512.01355
