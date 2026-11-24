---
bibkey: zhouliu2025simplexprojection
authors: Weimi Zhou and Yong-Jin Liu
year: 2025
title: "Fast projection onto the intersection of simplex and singly linear constraint and its generalized Jacobian"
doi: 10.61208/pjo-2025-002
url: https://arxiv.org/html/2310.10388v3
claim: "Euclidean projection onto the probability simplex intersected with one linear half-space reduces to simplex projection of a shifted input and a scalar equation for the multiplier."
strata_touched:
  - D5/S3/Fourier/Concentration/ClippedMomentWeights
license: citation-only
triage: anchor
---

# Projection onto a simplex with a lower moment bound

## Verified locator

- Published DOI [10.61208/pjo-2025-002](https://doi.org/10.61208/pjo-2025-002).
- Versioned preprint https://arxiv.org/html/2310.10388v3. See problem (P) in
  Section 1, Proposition 2.2, equation (3.4), and Propositions 3.1 and 3.2.

## Constrained projection

In Zhou and Liu's problem (P), take the point to project to be zero, the
half-space coefficient vector to be `-c`, and its right-hand side to be
`-a`. The feasible simplex weights then have real moment at least `a`.
Minimizing the squared Euclidean norm is minimizing the sum of squared
weights. Proposition 2.2 gives the threshold formula for simplex
projection. Equation (3.4) applies it to the shifted input and
Propositions 3.1 and 3.2 give the scalar moment equation and its relation
to the constrained solution.
[Original statement and equation (3.4)](https://arxiv.org/html/2310.10388v3#S3.SS1)

With the above signs the shifted projection is proportional to the
positive part of `α + σ cᵢ` for `σ ≥ 0`. When `α + σ C > 0`, divide the
affine expression by this positive quantity and normalize to total mass
one. This gives the positive part of `1 − t(C − cᵢ)` with
`t = σ/(α + σ C)`. For a lower bound at or below the uniform mean, the
unshifted projection gives uniform weights. At the maximum moment,
the feasible vectors are concentrated on the maximizing indices and
the minimum splits the mass equally there.

The Lean theorem uses an attained anchor `C ≥ a` and proves attainment
with a finite bound on the normalized parameter. Its energy identity
retains both the moment difference and the contributions from clipped
coordinates. The cyclic application uses one real character mode.
