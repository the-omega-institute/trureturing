---
bibkey: giacomelli2026logconcavity
authors: P. Giacomelli
year: 2026
title: "Log-Concavity and Infinite Log-Concavity of Linear Recurrent Sequences with Linear Coefficients via Companion Matrix Methods"
doi: 10.48550/arXiv.2604.14391
url: https://arxiv.org/abs/2604.14391v1
claim: "Section 7 (1) asks whether the cone of infinitely log-concave initial data is convex for d ≥ 3."
strata_touched:
  - D5/S0/Certificates/GiacomelliLogConcaveConeNonconvex
license: citation-only
triage: anchor
---

## Verified locator

DOI: https://doi.org/10.48550/arXiv.2604.14391

Source: https://arxiv.org/abs/2604.14391v1

Equation (3), printed page 2; Definition 2.1, printed page 3; Section 7 (1),
printed page 13.

## Source statements

Equation (3) reads
`a_{n+1} = Σ_{k=0}^{d−1} (p_k n + q_k) a_{n−k}, n ≥ d − 1`,
with `p_k, q_k ∈ ℝ` and initial data `(a_0, …, a_{d−1}) ∈ ℝ^d`.

Definition 2.1 states:

> Let (aₖ)ₖ∈ℕ be a sequence of real numbers. The log-concave operator L is defined by L(aₖ) = (bₖ), bₖ = aₖ² − aₖ₊₁aₖ₋₁. The sequence (aₖ) is log-concave if bₖ ≥ 0 for all k. For i ≥ 1, (aₖ) is i-fold log-concave if Lⁱ(aₖ) ≥ 0, and ∞-log-concave if Lⁱ(aₖ) ≥ 0 for all i ∈ ℕ.

Section 7 (1) asks:

> (Cone of initial data for variable coefficients.) Proposition 3.4 gives a matrix condition on v₀ for log-concavity of a general P-recursive sequence. Characterize the geometry of the cone C∞ = {v₀ : Lⁱ(aₙ) ≥ 0 ∀ n, i} for d ≥ 3. Is it convex? Simply connected?

## Mathematical scope

The recurrence uses increasing-order initial coordinates and the substitution
`m = n + 1`. Natural subtraction is truncated. The iterated operator is
tested at interior indices `i ≤ n`, so all indices of its dependence window
exist. Iteration zero requires nonnegative terms. The two positive geometric
solutions used in the refutation also satisfy the version starting at i = 1.

The affirmative convexity assertion quantifies over all real coefficients
and every order d ≥ 3. For d = 3, p = (1, −3, 2) and q = (3, −2, 0),
initial data (1, 1, 1) and (1, 2, 4) generate 1 and 2ⁿ. Every positive
interior iterate vanishes for each. Their midpoint (1, 3/2, 5/2) has first
log-concavity determinant −1/4 at index 1. The source's characterization
and simple-connectedness questions remain open here.

Literature-search completeness and absence of an earlier answer are
ASSUMED-UNVERIFIED; the searched scope is recorded in issue #18698.
