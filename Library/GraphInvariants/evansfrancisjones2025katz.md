---
bibkey: evansfrancisjones2025katz
authors: Emily J. Evans, Amanda E. Francis and Rebecca D. Jones
year: 2025
title: Katz similarity index comparisons
doi: 10.48550/arXiv.2509.02874
url: https://arxiv.org/abs/2509.02874v1
claim: "The cut-off values α_n converge to 1/√5 from above."
strata_touched:
  - D5/S1/Recurrence/KatzCutoff
license: citation-only
triage: anchor
---

# Katz similarity on paths

## Verified locator

DOI: 10.48550/arXiv.2509.02874

Source: https://arxiv.org/abs/2509.02874v1

Definition 1 (page 2):

> Let G be a simple graph with adjacency matrix A, and let 0 < α < 1/ρ(A). Then the Katz matrix of G at α is given by K_G(α) = αA + α²A² + α³A³ + ⋯ = ∑_{t=1}^∞ αᵗAᵗ = (I − αA)⁻¹ − I and the Katz similarity index at α between vertices i and j of G is given by K_G(α)_{i,j}.

Section 4.2 (page 13):

> Consider the polynomial ₙp_j(α) = min_i K_{P_n}(α)_{i,i+j} − max_i K_{P_n}(α)_{i,i+j+1}.

Theorem 19 and the cut-off definition (page 16):

> For n − j ≥ 5, ₙp_j(α) has a root between 1/√5 and 1/2.

> We call the roots α_n of the polynomials ₙp₁ the cut-off values for the path graph P_n.

Conjecture 4 (pages 3 and 17):

> The cut-off values α_n converge to 1/√5 from above.

The Lean indices are zero-based. The minimum for j=1 ranges over Fin (n−1),
and the maximum for j=2 ranges over Fin (n−2). Entries outside the natural-index
range are extended by zero; these extra values are excluded by the two finite ranges.
The claim includes root existence for every n≥6 and convergence of every sequence
of roots in (0,1/2), without a monotonicity hypothesis on that sequence.

## Literature boundary

The source supplies the recurrence and path-entry identities, the finite extrema,
and Theorem 19. The repository proof supplies the convergence in Conjecture 4.
The literature screen recorded in issue #20122 found no settlement among the
inspected versions, title and author searches, tridiagonal-inverse reference,
and related papers. Completeness of that screen is ASSUMED-UNVERIFIED.
