---
bibkey: tropp2012matrix
authors: Joel A. Tropp
year: 2012
title: User-Friendly Tail Bounds for Sums of Random Matrices
doi: 10.1007/s10208-011-9099-z
url: https://arxiv.org/abs/1004.4389v7
claim: Matrix Bernstein controls independent centered self-adjoint sums under an almost-sure norm bound and a matrix variance bound.
strata_touched:
  - D5/S3/Quantum/Dynamics/HamiltonianEffectCompletionGenerator
license: citation-only
triage: anchor
---

# Matrix concentration for a supervised rollout score

## Source and locator

Foundations of Computational Mathematics 12, 389–434 (2012). Publisher metadata and parsed arXiv:1004.4389v7 were checked. Theorem 1.4, on PDF page 4, is the matrix Bernstein inequality used here. A screenshot request failed; the theorem was read from parsed text.

## Exact use and verified hypotheses

The unified theory's Section 14 constructs a symmetric sample score Z from one independently sampled trajectory, its initial feature, and one independent uniform evaluation time. Assuming bounded target and initial-feature norms gives ||Z|| at most K0, ||Z-EZ|| at most 2K0, and E[(Z-EZ)^2] at most K0^2 I.

Applying the source to both signs and then to a finite candidate set gives the stated uniform score error. A rank-constrained variational comparison converts it to a risk-regret budget. This application does not claim a new concentration inequality.

Independence concerns different records, not different candidate models computed from the same records. Empirical maxima cannot substitute for almost-sure bounds, and an adaptively trained initializer requires a separate generalization argument or independent sample split. The existing Lean declaration does not prove this concentration theorem or its application.
