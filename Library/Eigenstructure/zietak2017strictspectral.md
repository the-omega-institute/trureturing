---
bibkey: zietak2017strictspectral
authors: Krystyna Ziętak
year: 2017
title: From the strict Chebyshev approximant of a vector to the strict spectral approximant of a matrix
doi: 10.4064/bc112-0-16
url: https://doi.org/10.4064/bc112-0-16
claim: Conjecture 1.1 asserts convergence of Schatten-p residuals to the lexicographically minimal singular-value residual.
strata_touched:
  - D5/S3/Quantum/NormCompression/StrictSpectralPolyaRefutation
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.4064/bc112-0-16

Source: https://doi.org/10.4064/bc112-0-16

## Source statement

Page 309, Conjecture 1.1:

> Let ℳ be a linear subspace of ℂᵐˣⁿ and let Bₚ ∈ ℳ be the cₚ-approximant to A ∈ ℂᵐˣⁿ. As p tends to ∞, the matrix Rₚ = A − Bₚ converges to A − B⁽ˢᵗ⁾, where B⁽ˢᵗ⁾ is the strict spectral approximant to A.

Page 309, definition:

> A matrix B⁽ˢᵗ⁾ ∈ ℳ is a strict spectral approximant to a matrix A if the vector σ(R⁽ˢᵗ⁾) of the ordered singular values of the residual matrix R⁽ˢᵗ⁾ = A − B⁽ˢᵗ⁾ is minimal with respect to the lexicographic ordering in the set of vectors {σ ∈ ℝᵗ : σ = σ(A − X), X ∈ ℳ} (see [106]).

The finite rectangular complex matrix carrier and decreasing, zero-padded singular values are used in the Lean statement. The quantifier over all choices of cₚ-approximants is encoded by a function of the real exponent p with minimization required for p > 1.

Page 308:

> Thus for 1 < p < ∞ the cₚ-approximant B = Bₚ ∈ ℳ to A satisfying (1.1) is unique.

Equation (1.1) is ‖A − B‖ = min {‖A − X‖ : X ∈ ℳ}.
