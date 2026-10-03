---
bibkey: coulter2025weingarten
authors: Coulter, Xavier; Do, Norman
year: 2025
title: From Weingarten calculus for real Grassmannians to deformations of monotone Hurwitz numbers and Jucys–Murphy elements
doi: 10.48550/arXiv.2506.04002
url: https://arxiv.org/abs/2506.04002v1
claim: Conjecture 5.4(a) asserts commutation of the b-deformed Jucys–Murphy operators on the cyclic orbit of the identity pair partition.
strata_touched:
  - D5/S0/Certificates/Combinatorics/DeformedJucysMurphyNoncommutation
license: citation-only
triage: anchor
---

# Deformed Jucys–Murphy operators

Conjecture 5.4(a), page 34, states:

> The 𝒥-operators commute when restricted to 𝒳(k) — that is, 𝒥ₘ 𝒥ₙ (v) = 𝒥ₙ 𝒥ₘ (v) for 1 ⩽ m ⩽ n ⩽ k and for all v ∈ 𝒳(k).

Definition 5.3 on the same page states:

> For k a positive integer, let 𝒳(k) = ⟨𝒥₁, 𝒥₂, …, 𝒥ₖ⟩ · 𝔢ₖ ⊆ 𝒱ₖ. That is, 𝒳(k) is the orbit of 𝔢ₖ under the action of the algebra of 𝒥-operators.

Definition 5.1, page 33, states:

> For k a positive integer, let 𝒱ₖ = ℂ(b)[𝒫ₖ] be the vector space with basis the set of pair partitions of {1, 2, …, 2k}. Define the b-deformed Jucys–Murphy operators 𝒥₁, 𝒥₂, …, 𝒥ₖ: 𝒱ₖ → 𝒱ₖ by 𝒥ᵢ(m) = ∑_(a=1)^(2i−2) ω^(b)((a 2i−1) · m, m) (a 2i−1) · m, where m ∈ 𝒫ₖ and ω^(b) is the weight function of Definition 4.1. We interpret the formula for i = 1 as 𝒥₁ = 0 and refer to these operators collectively as 𝒥-operators.

Definition 4.1, page 21, specifies the charges and weights:

> To each vertex v ∈ Γ(m), assign a charge q(v) ∈ {+, −} such that the vertex with the largest label in each cycle is assigned + and such that each edge in Γ(m) is incident to one vertex with positive change and one vertex with negative charge.

> Set ω^(b)(m,n) = 1 if q(i) = q(j) and set ω^(b)(m,n) = b if q(i) ≠ q(j).

The source's “positive change” is retained literally. In the operator
formula the output matching is the first argument of the weight function;
its graph supplies the charges. The pair-partition action is relabelling:
“the pair {a, b} appears in the pair partition m if and only if the pair
{σ(a), σ(b)} appears in the pair partition σ · m”. The identity
partition has consecutive pairs.

The formal encoding shifts labels down by one and uses fixed-point-free
involutive partner maps on `Fin (2*k)`. Coefficient functions on this finite
carrier represent the vector space. The scalar field is `RatFunc ℂ`, with
`RatFunc.X` as the indeterminate. The cyclic orbit uses `Algebra.adjoin`,
not the full vector space. The alternating walk implements the charge by
the parity of the first occurrence of the component maximum; its general
correspondence to the graph rule is explained mathematically in the
module and mirror, rather than asserted as a separate Lean theorem.

The refutation uses `k = 6`, `v = J_6 J_6 J_5 J_4 J_3 e_6`, and the target
pair partition `(1 5 | 2 7 | 3 9 | 4 11 | 6 10 | 8 12)`. The target
coefficients after `J_2 J_4` and `J_4 J_2` evaluate at `b = 2` to `78` and
`81`. Polynomial transport through the injective map `ℤ[X] → ℂ(b)` makes
this a refutation with an indeterminate, rather than just a specialized
scalar example.

The published numerical checks for `k ≤ 5` do not decide `k = 6`. Failure
of commutation obstructs the simultaneous eigenbasis conjectured in
5.4(b). Conjecture 5.7(b) requires an ordering convention for products of
these operators; the paper itself notes that its order-independent
interpretation depends on 5.4(a). This refutation alone does not settle
5.7(a), 5.8, or the already proved ordered identities in Proposition 5.9.

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.2506.04002
- Source: https://arxiv.org/abs/2506.04002v1
