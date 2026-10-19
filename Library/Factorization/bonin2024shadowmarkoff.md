---
bibkey: bonin2024shadowmarkoff
authors: Nathan Bonin
year: 2024
title: Conditions of positivity on a shadow Markoff tree
doi: 10.48550/arXiv.2403.07668
url: https://arxiv.org/abs/2403.07668
claim: "Conjecture 1 identifies the quadrilateral of initial shadows yielding nonnegative integer shadow Markoff trees."
strata_touched:
  - D5/S3/Factorization/BoninShadowMarkoffPositivity
license: citation-only
triage: anchor
---

<!-- GID: D5/L/Factorization/bonin2024shadowmarkoff -->

# Positivity on a shadow Markoff tree

## Verified locator

DOI: https://doi.org/10.48550/arXiv.2403.07668

Source: https://arxiv.org/abs/2403.07668

Nathan Bonin, *Conditions of positivity on a shadow Markoff tree*,
J. Integer Sequences 27 (2024), Article 24.8.3; arXiv:2403.07668v2.
The journal landing page supplies no separate journal DOI; the DOI above
identifies the arXiv article.

## Conjecture 1

Page 3, Conjecture 1:

> Every triple (A, B, C) of positive integer solutions to (3) can be obtained
> from the initial triple (7) where (α, β, γ) are positive integers such that
> (α : β : γ) ∈ ℚP² are the rational points that belong to the quadrilateral
> with vertices {(0 : 0 : 1); (1/2 : 0 : 1) ≡ (1 : 0 : 2); (1 : 1 : 1); (0 : 2 : 1)}
> depicted in the following figure
>
> via mutations (5) and permutations along the Markoff tree.

Page 3 describes the equivalent tree property:

> It can be reformulated in terms of the initial triple (7) such that under
> every series of mutations along the Markoff tree the triple (α, β, γ) remain positive.

Section 5, page 9:

> the 2 mandatory beginning mutations (to the right, then to the left)

## Mathematical interpretation

The six coordinates are ordered as [a, α, b, β, c, γ], exactly as in
Section 5's `path` code. The tree includes its root and the two mandatory
moves before every finite word in l and r. Equation (8) uses ℕ for all
six coordinates. The zero initial shadow triple is excluded because it
has no projective point; boundary vertices permit zero shadows. The chart
γ = 1 uses (α/γ, β/γ), with γ > 0, and the four affine vertices are
(0,0), (1/2,0), (1,1), (0,2).

Theorem 1 in the source places the positive initial points in some convex
polygon. The exact quadrilateral characterization strengthens that
conclusion for the rooted tree. No assertion about arbitrary independent
permutations at the root is included.

## Literature boundary

The source and Bonin's Reims thesis, NNT 2026REIMS005, Section 4.5,
state the conjecture without a proof. The screened arXiv, HAL, Semantic
Scholar and OpenAlex records and arXiv:2503.21872, 2402.19300 and
2507.19080 supplied no prior resolution. Exhaustive prior-art absence is
ASSUMED-UNVERIFIED: separate JIS citation enumeration was rate-limited.
