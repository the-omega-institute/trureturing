---
bibkey: mandalmanna2026distance
authors: Santanu Mandal and Pallabi Manna
year: 2026
title: The Distance Laplacian and Distance Signless Laplacian Spectra of C-Graphs
doi: 10.48550/arXiv.2610.08599
url: https://arxiv.org/abs/2610.08599v1
claim: "Conjecture 5.5: For every connected 𝒞-graph G, every eigenvalue of D^Q(G) not in 𝒯^Q(G) satisfies mult_{D^Q(G)}(θ) ≤ ∇(G)."
strata_touched:
  - D5/S3/Combinatorics/SpectralGraph/MandalMannaDQDilworthRefutation
license: citation-only
triage: anchor
---

# Distance signless multiplicity and the Dilworth number

## Verified locator

DOI: 10.48550/arXiv.2610.08599

Source: https://arxiv.org/abs/2610.08599v1

## Source statements

Conjecture 5.5, page 11: “For every connected 𝒞-graph G, every eigenvalue of D^Q(G) not in 𝒯^Q(G) satisfies mult_{D^Q(G)}(θ) ≤ ∇(G).”

Definition 5.1, page 10: “For a graph G, define u ≼ v if N(u) ⊆ N[v] (equivalently, N[u] ⊆ N[v] when u ∼ v, and N(u) ⊆ N(v) when u ≁ v).” The same definition states: “A set of vertices pairwise related by ≼ is a chain; a set of pairwise unrelated is an antichain.” It continues: “The Dilworth number ∇(G) is the minimum number of chains needed to cover V(G), equivalently (by Dilworth’s theorem) the maximum size of an antichain.”

Section 1, page 2:

\[
C(\alpha_1)=\overline{K_{\alpha_1}},\qquad
C(\alpha_1,\ldots,\alpha_i)=
\overline{C(\alpha_1,\ldots,\alpha_{i-1})\cup K_{\alpha_i}}\quad(i\ge2).
\]

“where ∪ denotes disjoint union and the overline denotes graph complementation. They call G = C(α₁,…,αₘ) a 𝒞-graph, and (α₁,…,αₘ) its creation sequence.”

Section 1, page 1: “The sum of the distances between a vertex v and every other vertex in G is known as the transmission of v and denoted by Tr(v), that is,” followed by the row-sum display. That display has inconsistent dummy variable names; the preceding sentence fixes the row sum at the chosen vertex. The same page gives “D^Q(G) = Tr(G) + D(G)” for the distance signless Laplacian.

Section 2, page 3: “Throughout, G is a connected 𝒞-graph on n vertices with creation sequence (α₁,…,αₘ), nᵢ = α₁+⋯+αᵢ, and αₘᵢₙ = min₁≤ᵢ≤ₘ αᵢ and m is even.” The source uses positive natural block sizes.

Section 5, page 11:

\[
\mathcal T^Q(G)=\{\operatorname{Tr}_i-1:i\text{ odd},\ \alpha_i\ge2\}
\cup\{\operatorname{Tr}_i-2:i\text{ even},\ \alpha_i\ge2\}.
\]

## Encoding and scope

The finite vertex type is built by disjoint sums of the source blocks.
The list is reversed at the boundary to make the recurrence structural;
block indices remain one-based chronological indices. Graph complement,
disjoint union, native shortest-path distance, characteristic polynomial,
root multiplicity and eigenspaces use Mathlib objects. A chain cover assigns
each vertex a label in `Fin k`, with comparable vertices in each fiber.
The infimum over feasible sizes is taken in extended naturals, where an
empty feasible set has value infinity. On the finite graphs quantified by
the conjecture, singleton chains provide a finite cover.

The Lean refutation uses eight singleton blocks, a connected graph with a
universal vertex and a single vicinal chain. Two independent modes of the
distance signless matrix have eigenvalue 8. Its algebraic multiplicity is
at least two, while the Dilworth number is one and the local-exception set
is empty. Parameterized shifted-matrix kernel identities and independence
are proved for all R ≥ 1; their identification with native recurrence graphs
is formalized only at R = 2. The infinite native-graph extension and exact
multiplicity two uniformly remain open.

The refutation invalidates the universal D^Q bound and its interpretation
in Remark 5.6. It does not refute the source's D^L statement, local-mode or
quotient formulas, or Example 5.4. No amended universal bound is asserted.

## Computed corroboration

The exact checker is in `the-omega-institute/trureturing-experiments`,
commit `daff737da5c5f9b6946de114e69753ecde01e652`, at
`docs/reports/mandal-manna-dq-dilworth/check.py`.
Its SHA-256 is
`413df9e09713c58a2de0802c3dbe4c372a66cc4caa82c9b0a0c3430395225d9e`.
Running `python3 check.py` on the exact file gives exit 0 and
`ALL_CHECKS_OK`: the checker validates source-family members r = 1,…,12,
with nullity exactly two in each tested member, and reproduces Example 5.4.
These finite computations are separate from the Lean proof.

Literature completeness is ASSUMED-UNVERIFIED. The bounded search recorded
in #23915 found no settlement in the inspected texts; citing-work discovery
was rate-limited and several older full texts were unavailable.
