---
bibkey: badica2026jaccardlattices
authors: C. Bădică and A. Bădică
year: 2026
title: "On the Triangle Inequality for the Jaccard Distance in Arbitrary Lattices"
doi: 10.48550/arXiv.2608.18194
url: https://arxiv.org/abs/2608.18194v1
claim: "Section 8 asks whether supermodularity and log-submodularity, or supermodularity of f and 1/f, suffice for the generalized Jaccard triangle inequality on arbitrary lattices."
strata_touched:
  - D5/S3/Combinatorics/Lattices/BadicaJaccardArbitraryLattices
license: citation-only
triage: anchor
---

# Generalized Jaccard distances on lattices

## Verified locator

DOI: 10.48550/arXiv.2608.18194

Source: https://arxiv.org/abs/2608.18194v1

C. Bădică and A. Bădică, “On the Triangle Inequality for the Jaccard Distance in Arbitrary Lattices”, arXiv:2608.18194v1 (18 August 2026).

## Source statements

Definition 3, page 3:

> If f(X) > 0 for all X ∈ L, then f is strictly positive.

> f is submodular if and only if: f(X) + f(Y) ≥ f(X ∨ Y) + f(X ∧ Y) ∀X, Y ∈ L

> If f is strictly positive and log ∘ f is submodular, then f is log-submodular.

> f is supermodular if and only if: f(X) + f(Y) ≤ f(X ∨ Y) + f(X ∧ Y) ∀X, Y ∈ L

> f is monotone if and only if: f(X) ≤ f(Y) ∀X, Y ∈ L such that X ≤ Y

Equation (17), page 5:

> d_{f,J}(A, B) = 1 − f(A ∧ B)/f(A ∨ B)

Section 8, page 12, second problem:

> While we established metricity for supermodular and log-submodular valuations, the proof relies on the lattice being both relatively complemented and distributive. It is still unknown whether the standard generalized Jaccard formula holds up to the triangle inequality for these valuations on arbitrary lattices that lack those two specific traits.

Section 8, page 12, fourth problem:

> The reverse of this statement remains untested: if f and 1/f are supermodular, is that enough on its own to guarantee the triangle inequality? Also, it is unclear if the stricter log-submodularity constraint used in Theorem 2 is actually required, or if it can be loosened to match the more basic necessary conditions established later in the paper.

## Scope

The two formal conclusions retain strict positivity and monotonicity. One assumes supermodularity of f and its pointwise reciprocal. The other assumes supermodularity and log-submodularity, which imply reciprocal supermodularity. Both conclude only the triangle inequality on arbitrary lattices, without finiteness, distributivity, or complementation. Separation and the symmetric-difference question are not asserted.

The preregistration and literature screen are at https://github.com/the-omega-institute/trureturing/issues/20617. Literature completeness is ASSUMED-UNVERIFIED; the recorded OpenAlex and Semantic Scholar requests returned HTTP 429.
