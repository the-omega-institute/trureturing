---
slug: reyes-dalfo-fiol-2024-new-laplacian-layer-maxima
bibkey: reyes2023tokenspectra
doi: 10.1007/s40590-023-00583-3
url: https://arxiv.org/html/2310.16929v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/TokenGraphLaplacianRadiusRefutation.tokenGraph
---

# Successive new Laplacian layer maxima of token graphs

## Problem

M. A. Reyes, C. Dalfó and M. À. Fiol, *On the spectra and spectral radii
of token graphs*, arXiv:2310.16929v1, Section 3, Definition 3.1 and
Conjecture 3.3; journal version, *São Paulo Journal of Mathematical
Sciences* (2024), DOI 10.1007/s40590-023-00583-3, Section 3:

> Conjecture 3.3. For any graph G, ρ₁(G) ≤ ρ₂(G) ≤ ⋯ ≤ ρ⌊n/2⌋(G).

Here G is a finite simple unweighted undirected graph of order n. The source
uses the ordinary real Laplacian D−A. The vertices of F_j(G) are all
j-element subsets of V(G), with an edge precisely when their symmetric
difference is an edge of G. F_0(G) is the singleton empty configuration.
Writing Sp_j for the full Laplacian spectral **multiset**, Definition 3.1
sets Δ_j = Sp_j − Sp_(j−1) by multiset subtraction and ρ_j = max Δ_j,
for 1 ≤ j ≤ floor(n/2). Thus the conjecture quantifies every
1 ≤ k < floor(n/2) and asserts ρ_k ≤ ρ_(k+1).
The source's connected-graph convention is satisfied by the counterexample.

## Motivation

The existing frozen `tokenGraph` definition models actual token subsets
and moves. Full-sector spectral maxima and new-layer maxima are different
quantities: inherited eigenvalues remain in the former and are removed,
with their multiplicities, from the latter. This dossier addresses only
Conjecture 3.3, not the neighboring minimum conjecture or a full-radius
characterization.

## Gap

Issue [#23401](https://github.com/the-omega-institute/trureturing/issues/23401)
preregisters the whole original Conjecture 3.3. The bounded all-state
qualification found no equivalent target registered to another owner and
no complete posted answer in its searched scope. Closed #12457 and
PR #12611 concern arXiv:2610.00500 Conjecture 1.1, a different assertion
about full Laplacian radii. This is not a worldwide absence or priority claim.

## Route

Take the connected star K₁,₃ on four vertices and k=1. The actual zero-,
one- and two-token spectral multisets are

| j | Sp_j | Δ_j | ρ_j |
| --- | --- | --- | --- |
| 0 | {0} | — | — |
| 1 | {0,1,1,4} | {1,1,4} | 4 |
| 2 | {0,1,1,3,3,4} | {3,3} | 3 |

The two-token graph is C₆. Explicit equivalences enumerate all token
subsets; entrywise Laplacian identities and complete invertible rational
eigenbases prove these entire spectra through characteristic-polynomial
roots with multiplicity. Consecutive multiset subtraction then gives
4 > 3. Since 1 ≤ 1 < floor(4/2), this contradicts the original universal
statement. The proof of nonempty layers covers every graph and every
1 ≤ j ≤ floor(n/2), using the strict binomial-cardinality increase, so
ρ is an actual maximum throughout its source domain.

Dongsheng Wei, *Generators of stability-preserving semigroups, spectral
gaps, and classical ground-state computation*, arXiv:2609.26802v1 §4.6
and v2 §7, supplies prior star/two-token-cycle and full-sector spectral
ingredients. The source note attributes them; no new spectral method is claimed.

## Falsifier

A mismatch in the token-subset enumeration, an incorrect D−A matrix,
a missing eigenvalue multiplicity, set subtraction in place of multiset
subtraction, or a source restriction excluding this connected star would
invalidate this refutation. The matrices and full eigenbases are checked
in Lean. In particular the full positive-level radii are both 4; comparing
those instead would not establish the asserted new-layer decrease.

## Evidence

The settling endpoint is
`D5.S3.Combinatorics.Graph.TokenGraph.NewLayerMaximaRefutation.result`.
Its literal compiled type is `Not claim`; `claim : Prop` retains every n,
every `SimpleGraph (Fin n)` with decidable adjacency, and every
1 ≤ k < n/2. There is no order cap, certificate premise or nonemptiness
assumption. The source and journal readings agree on Definition 3.1 and
Conjecture 3.3.

The module contains four authored public definitions (`spectrum`, `layer`,
`rho`, `claim`), the sole designated public theorem `result`, ten private
helper lemmas consumed by `rho` or `result`, and two compiler-generated
companions. Its checked axiom closure is contained in
{`Classical.choice`, `Quot.sound`, `propext`}, with no `sorry` or new axiom.
The canonical Scribe attaches one `OpenProblemResolutionClaim` of kind
`Refuted` to this endpoint and cites the Library source identity.

## Triage

Tier 1, `theorem`; admission basis `open-problem-resolution` under #23401.
The proof shape is bind-only and the escape witness is none: finite exact
matrix calculations and existing spectral machinery discharge the entire
external conjecture's negation. Every helper is consumed; no standalone
method or positive-instance theorem is packaged. The designated utility
refutation is exempt from four-slot registration; there are no other
new public theorem audit targets. The utility is `certified-instance`
with basis `refutes`, bound to this module's literal `claim` and `result`.

## ASSUMED-UNVERIFIED

The supplied supplier-first and all-state qualification evidence has bounded
search scope. It establishes neither worldwide novelty nor exhaustive
absence of an earlier settlement. The star and cycle ingredients are
attributed to Wei. Selected Lean/report checks establish only their selected
modules and imports; final independent CLI architecture, quality and tests
reviews and exact-head required CI remain separate publication gates.
This dossier grants no solve credit, issue closure or merge authorization.
