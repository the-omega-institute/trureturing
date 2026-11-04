---
bibkey: arizmendi2020energygame
authors: Gerardo Arizmendi and Octavio Arizmendi
year: 2020
title: The graph energy game
doi: 10.1016/j.dam.2023.01.030
url: https://arxiv.org/abs/2012.14114v2
claim: "Conjecture 3.10: For the energy game, the Shapley value is in the core."
strata_touched:
  - D5/S3/Combinatorics/SpectralGraph/ArizmendiEnergyGameShapleyRefutation
license: citation-only
triage: anchor
---

# The graph energy game

## Verified locator

DOI: 10.1016/j.dam.2023.01.030

Source: https://arxiv.org/abs/2012.14114v2

The quoted source is arXiv v2, revised 18 March 2021; v1 was submitted
28 December 2020. The journal citation is Discrete Applied Mathematics 330
(2023), 128–140. The journal full text has not been verified.

## Source statements

Conjecture 3.10, page 8: “For the energy game, the Shapley value is in the core.”

Definition 3.1, page 5: “Let G = (V, E) be a simple undirected graph.
For each subset S ⊂ V let w(S) := 𝓔(I(S)) where I(S) is the graph induced
by S. We denote (V, w), the energy game on G.”

Definition 2.7, page 4: “The core of a game (N, w), denoted by C(w) is the
set of imputations that are group rational. That is,” followed by
“C(w) = {x| x(S) ≥ w(S) for each S ⊂ N and x(N) = w(N)}”.
The same page states: “For a payoff distribution x and a coalition S, we use
the notation x(S) = ∑_{i∈S} xᵢ.”

Section 2.4, page 4: “The Shapley value is the only value that satisfies the
axioms of efficiency, symmetry, additivity and null player, it is well known
that actually the Shapley value is given by” followed by
“φᵢ(w) = ∑_{S⊂N∖{i}} |S|!(n − |S| − 1)!(w(S ∪ {i}) − w(S))/n!”

## Encoding and scope

The graph is `SimpleGraph (Fin n)` for every natural size, including zero.
Coalitions are finite sets, with every subset included in the powerset sum.
The payoff total is the finite sum, written directly in the core predicate.
The characteristic function uses the existing ordinary adjacency
`graphEnergy (G.induce (S : Set V)) .adjacency`: absolute Hermitian adjacency
eigenvalues counted with multiplicity and center zero. Each Shapley
coefficient is the source's factorial expression, coerced to real numbers.

The refutation uses the complete bipartite graph K₂,₅₀, supported by the
family K₂,ₘ for m ≥ 50. A scarce-side vertex receives more than its marginal
contribution to the grand coalition; efficiency and the coalition excluding
that vertex cannot both meet the core conditions.

The source's vertex-energy allocation theorem (Theorem 3.5 and Corollary
3.6) concerns a different allocation. Proposition 3.11's marginal lower
bound and Proposition 4.13's statement for the 2-energy game do not depend
on Conjecture 3.10. These published results are not freshly formalized here.

Literature completeness is ASSUMED-UNVERIFIED. The bounded screen in
issue #21951 found no settlement in the retrieved texts; the journal full
text and some citing works remain unread.

## Computed corroboration

The exact-arithmetic checker is in
`the-omega-institute/trureturing-experiments`, commit
`482b7177598d82c15ee82daca692752e471ee567`, at
`docs/reports/arizmendi-energy-game-shapley/check.py`.
Its SHA-256 is
`5e2feaa724951623c0a3e8730b1a9727c71f70ab2d6f434869d5a9fdccc20125`.
Running `python3 check.py` with SymPy 1.14.0 exits 0 with
`ALL_CHECKS_OK`. It checks the complete bipartite witness and the source's
three-vertex example using exact arithmetic. This computation is separate
from the Lean proof.
