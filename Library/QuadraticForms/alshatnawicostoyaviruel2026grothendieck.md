---
bibkey: alshatnawicostoyaviruel2026grothendieck
authors: I. Alshatnawi; C. Costoya; A. Viruel
year: 2026
title: "On the Grothendieck Ring of Finite-Dimensional Non-Degenerate Evolution Algebras"
doi: 10.48550/arXiv.2607.15154
url: https://arxiv.org/abs/2607.15154v1
claim: "Definitions 2.1, 2.2 and 2.4 define directed graphs, signed paths and the all-cycle balance; Theorem 6.1 assumes nondegeneracy."
strata_touched:
  - D5/S3/QuadraticForms/EvolutionAlgebras/DegenerateGraphBalanceRefutation
license: citation-only
triage: anchor
---

## Verified locator

DOI: https://doi.org/10.48550/arXiv.2607.15154

Source: https://arxiv.org/abs/2607.15154v1

Definitions 2.1, 2.2 and 2.4 are on page 4. Theorem 6.1 concerns nonzero
nondegenerate evolution algebras; it does not include the degenerate example.

## Directed paths and balance

Definition 2.1: “A graph is a pair Γ=(V,E) consisting of a finite set of vertices V
and a set of edges (or arrows) E⊆V×V.”

Definition 2.2: “A path in Γ is a sequence
γ=(v₀,e₁,v₁,…,vₙ₋₁,eₙ,vₙ), n ≥ 0,
with v₀,…,vₙ∈V and e₁,…,eₙ∈E such that, for each i∈{1,…,n}, either
eᵢ=(vᵢ₋₁,vᵢ) (the edge is traversed forwards) or eᵢ=(vᵢ,vᵢ₋₁)
(traversed backwards). A (non-simple) cycle is a path with v₀=vₙ. The balance
of γ is the integer b(γ)=#{ i : eᵢ=(vᵢ₋₁,vᵢ) }−#{ i : eᵢ=(vᵢ,vᵢ₋₁) }”.

Definition 2.4: “The balance of Γ is the greatest common divisor of the
absolute values of the balances of its cycles,
b(Γ)=gcd{ |b(γ)| : γ a cycle in Γ }.”

The displayed two-cardinality formula counts a loop in both sets. The graphs
in DegenerateGraphBalanceRefutation have no loops. Cycles retain actual
arrows even when both opposing arrows exist. The gcd uses every finite
closed path, including paths of length zero, and is zero if every balance
vanishes. The integer ideal-generator construction expresses this gcd
without a finite cycle-length cutoff.

## The final balance question

Kaygorodov, Martín González and Viruel, *Evolution algebras: a survey of results
and a list of open problems*, arXiv:2610.22248v1,
https://arxiv.org/abs/2610.22248v1, Question 27, page 24:
“Is the balance independent of the natural basis for arbitrary (possibly degenerate) evolution algebras?” Their section 1.1, page 3 states:
“Unless stated otherwise, algebras are finite-dimensional.”

The survey source has its own note, kaygorodov2026evolution. The graph and
balance definitions above supply the meanings of the terms in that question.
The refutation concerns the final question and does not contradict the
nondegenerate invariance theorem or the perfect-algebra basis-rigidity theorem.

The literature screen recorded in issue #21625 found no exact settlement
within its inspected scope. Exhaustive absence of a published settlement and
priority remain ASSUMED-UNVERIFIED.
