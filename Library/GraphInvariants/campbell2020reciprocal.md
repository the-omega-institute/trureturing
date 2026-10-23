---
bibkey: campbell2020reciprocal
authors: Kirsty Campbell
year: 2020
title: Group-Graph Reciprocal Pairs
doi: 10.48550/arXiv.2005.13566
url: https://arxiv.org/abs/2005.13566
claim: "The Conjecture on page 3 classifies irreducible group-graph reciprocal pairs as the two trivial cases, the four-cycle pair, or the k-star pairs of Theorem 1."
strata_touched:
  - D5/S3/Combinatorics/ReciprocalPairs/GroupGraphReciprocalRefutation
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.48550/arXiv.2005.13566

Source: https://arxiv.org/abs/2005.13566

The statement is the Conjecture on page 3 of arXiv:2005.13566v1. The definitions
of the cycle polynomial and fixed proper colourings are on page 1; reciprocity
and k-stars are on page 2; irreducibility is on page 3.

## Source statements

Conjecture, page 3 (verbatim):

> Conjecture: Let (Γ, G) be an irreducible reciprocal pair. Then one of the following hold:
> 1. (Γ, G) is one of the two trivial cases: (a) Γ is a null graph and G is any group with no odd permutations, (b) Γ is the complete graph with n vertices and G = Sn.
> 2. Γ is a 4-cycle and G ≅ Aut(Γ).
> 3. Γ is a k-star and G is defined in Theorem 1.

Irreducibility, page 3 (verbatim):

> A reciprocal pair (Γ, G) is irreducible is there is no non-trivial decomposition Γ = Γ1 ∪ Γ2 ∪ ... ∪ Γn and subgroups Gi ≤ G with Gi ≤ Aut(Γi) such that either
> 1. G = G1 × ... × Gn with each (Γi, Gi) a reciprocal pair,
> 2. Gi ≅ Gj and Γi ≅ Γj for all i ≠ j and G = G0 ≀ H for some H ≤ Sn and G0 ≅ Gi for all i.

Cycle polynomial, page 1: "The cycle polynomial of a finite permutation group G
acting on a set Ω of size n is" F_G(x) = Σ_{g∈G} x^{c(g)}, "where c(g) is the
number of cycles (including fixed points) of g on Ω."

Proper and fixed colourings, page 1: "A proper colouring of a graph is a map
from the vertex set to the set of colourings such that no two adjacent vertices
have the same colour." "The chromatic polynomial PΓ/g(x) is the polynomial
which counts proper colourings of Γ fixed by g."

Reciprocity, page 2: "We call a group-graph pair (Γ, G) a reciprocal pair if the
relation" PΓ,G(x) = (−1)^n F_G(−x) "holds for a simple graph Γ with n vertices
and where G is an automorphism group of Γ."

Automorphisms, page 4: "By definition, g is an element of the automorphism group
if and only if {i, j} and {g(i), g(j)} are both edges in Γ."

## Scope of the refutation

The witness is 3K₂ ⊔ 2K₄ with all internal clique permutations and an S₃ action
on the three K₂ components, coupled through its sign to the two K₄ components.
The decomposition predicate admits every decomposition permitted by the source
and additional ones. The listed-class predicate omits the group restrictions.
A refutation with these broader predicates therefore refutes the source conjecture.
The source's proved results about k-stars, including Theorem 1, do not require
this conjecture and are unaffected by its refutation.
