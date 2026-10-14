---
bibkey: greavesiversonjaspermixon2021orthogonalframes
authors: Gary R. W. Greaves, Joseph W. Iverson, John Jasper, Dustin G. Mixon
year: 2021
title: 'Frames over finite fields: Equiangular lines in orthogonal geometry'
doi: 10.48550/arXiv.2012.13642
url: https://arxiv.org/abs/2012.13642v2
claim: 'Definition 2.8 defines equiangular systems; Propositions 2.9 and 2.10 give Gerzon equality and the ETF parameter relation; Example 5.8 asks whether the dimension congruence restrictions on the parameter identity can be removed.'
strata_touched:
  - D5/S3/QuadraticForms/GerzonEqualityParameterIdentity
license: citation-only
triage: anchor
---

# Equiangular systems at Gerzon equality

## Verified locator

DOI: https://doi.org/10.48550/arXiv.2012.13642

Source: https://arxiv.org/abs/2012.13642v2

## Source statements

Definition 2.8, page 5:

> Let Φ = {ϕⱼ}ⱼ∈[n] be a sequence of vectors in a quadratic space W over F_q. For a, b ∈ F_q, Φ is called an (a, b)-equiangular system if:
> (i) ⟨ϕⱼ, ϕⱼ⟩ = a for every j ∈ [n],
> (ii) ⟨ϕᵢ, ϕⱼ⟩² = b for every i ≠ j in [n].

Example 5.8, page 21:

> The authors do not know how to construct an ETF with any of the parameters given in Table 4. In particular, every instance of Gerzon equality that we currently know satisfies the identity a² = (d + 2)b, but this equation does not occur anywhere in Table 4 (where b = 1). Proposition 2.10 implies that a² = (d + 2)b whenever Gerzon’s bound is saturated, d ≢ₚ 0, and d ≢ₚ 1. The authors do not know if these conditions can be removed.

Proposition 2.9, page 5, gives n ≤ C(d+1, 2) when a² ≠ b and states that equality forces an equiangular tight frame. Proposition 2.10, page 6, gives a(c − a) = (n − 1)b for an (a, b, c)-ETF.

## Relation to the formal statement

The field is finite with characteristic different from two. The quadratic space is represented by `Fin d → F`, with an arbitrary symmetric nondegenerate bilinear form B. The sequence is indexed by `Fin ((d + 1).choose 2)`. Its two equiangular conditions are exactly the diagonal equation and the squared off-diagonal equation. The identity is asserted for every d ≥ 2, including dimensions congruent to zero or one in the field. For d = 1 the off-diagonal condition is empty and b is unconstrained.

The unrestricted identity is derived in the repository; the source is cited for its definitions and question, rather than as a proof of that identity.

## Literature boundary

Shi–Liu–Kim–Solé, *Frames over finite fields and self-dual codes*, DOI 10.1007/s00200-023-00630-6, was read in full in the supplied literature screen; no answer to Example 5.8 was found there.

Wei–Luo, *Finite Tight Frames for Vector Spaces Over Finite Fields*, WCONF 2025, DOI 10.1109/WCONF64849.2025.11233785, remains ASSUMED-UNVERIFIED: no arXiv version was found, the IEEE page was blocked, and Firecrawl returned HTTP 402. Its contents have not been verified. The novelty statement is limited to “not found in the searched scope”.
