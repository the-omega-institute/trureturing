---
slug: adamson-positive-uniform-hierarchy
bibkey: adamson2026twoword
doi: null
url: https://arxiv.org/abs/2605.27183v1
triage: theorem
motivation_gids:
  - D5/S1/Words/GraphRepresentation/ExplicitNonTwoUniform
  - D5/S0/Diagonal/PigeonholeFiber
---

# Every positive-uniform adjacent class inclusion is proper

## Problem

Adamson, Dietz, Fleischmann, Huch and Sacher, *2-word-π-representable Graphs*,
arXiv:2605.27183v1, Conjecture 31, PDF p. 15, states:

> For each k ∈ ℕ, the inclusion 𝒢_k ⊆ 𝒢_(k+1) is proper.

The source convention starts ℕ at 1. For a finite simple graph G on V,
membership requires actual words w,v over V, each containing every vertex
exactly k times. For every distinct a,b, G.Adj(a,b) holds if and only if
their ordered two-letter List projections in w and v are equal. Positive
counts give both full alphabets. Single-word alternation and unions of word
representation languages are different models.

The exact full target has two clauses for every positive k: inclusion for
every finite graph, and existence of a finite graph on one and the same
carrier with a (k+1)-uniform representation and no k-uniform representation.
An assumed nonuniversality theorem, a fixed-k result, or vertex extension
alone does not settle either the full family or this named problem.

## Motivation

The earlier Dietz–Fleischmann–Huch–Sacher four-author contribution in IFIG
Report 2501, printed pp. 21–24 (PDF pp. 29–32), states the same assertion as
Conjecture 3.2 on printed p. 23. Its Open Problems section on p. 24 says
that only k=1 strictness was proved. Its actual body is available at
<https://www.informatik.uni-giessen.de/theorietag2025/2025-Theorietag35-Schotten.pdf>.
This is an earlier statement of the same problem, not a second question.

The full hierarchy asks for an unbounded proof about the representation
parameter. It is a Tier-1 proof/family target under issue
<https://github.com/the-omega-institute/trureturing/issues/12945>.
No global priority or established central-bottleneck claim is made.

## Gap

The declaration [`UniformVertexExtension.vertex_extension`](../D5/S1/Words/GraphRepresentation/UniformVertexExtension.lean)
provides the prescribed-neighborhood inference on the exact full carrier Option(V): a
positive k-uniform representation of G.comap(some) implies a (k+1)-uniform
representation of G. Its two actual lists are none^k w none NT and
none^k v N none T, where N,T enumerate old nonneighbors and neighbors
once each. The argument preserves old nonedges as well as edges and treats
both orders of each distinct pair. The empty old carrier is included.

The full target still needs an internal closed all-positive-k
nonuniversality proof, finite minimality, deletion and exact word/graph
relabeling, common-enumeration inclusion and the unconditional full consumer.
No coverage or resolution claim for Conjecture 31 follows from the extension.

## Route

Bounded cut signatures for the membership graph with m=64k² are a proposed
route to all-positive-k nonuniversality. Apply the existing arbitrary-cut
reconstruction and pigeonhole suppliers directly, retaining both actual
words and their exact counts. A finite minimum nonmember, together with
deletion and relabeling, must then provide a graph whose vertex deletion
belongs to G_k. The vertex-extension construction gives its G_(k+1)
representation on the same carrier. Appending a common once-each vertex
enumeration to both words supplies adjacent inclusion inside the full
consumer. Every premise of that consumer, including nonuniversality,
must be discharged by a closed proof.

## Falsifier

An equivalent prior settlement, a source-model mismatch or an unresolved
premise in the full consumer bars a named-problem settlement. An auxiliary
checkpoint contributes no solved-problem count. The extension would fail
its own statement if either actual list omitted a whole-carrier count or
the adjacency equivalence omitted a distinct pair, a nonedge, a reversed
pair, an empty old carrier or an arbitrary fresh neighborhood.

## Evidence

The primary v1 PDF has SHA-256
`f978a9e9de5cfaf8adfba59125cf16293b17f6b969f5f72594eab7a0cec719ca`.
The earlier IFIG PDF has SHA-256
`2aaa473fb648f515a69f9ce488bf557b83b4329eea009182f5131243eee81af2`.
Definitions and the relevant construction, graph-operation and hierarchy
proof sections were read from the actual bodies.

Bounded repository and authenticated issue/PR searches found the
preregistration and the earlier explicit G₂ obstruction, without an exact
hierarchy settlement or owner in that searched scope. Pinned Mathlib and
public Lean repository searches found no exact extension supplier. The
inspected public WordRepTensor source uses single-word alternation.

## Triage

`theorem` classifies the full unbounded family target. For the extension
checkpoint, `vertex_extension` has `proof_shape: content` and
`admission_basis: escape-witness`: the actual W,Z construction establishes
the public conclusion on its live proof path. `InG` is the necessary
positive-uniform representation definition. `utility: none` describes a
structural construction over arbitrary finite carriers and positive k,
with no bounded enumeration, checker, numerical reduction or certified
positive finite instance. The checkpoint is not an external open-problem
resolution and does not settle Conjecture 31.

## ASSUMED-UNVERIFIED

The same-title *Gradiva*, 8(9) (2022), pp. 528–533 citation is a bibliographic
match; neither its journal body nor the body associated with SSRN DOI
10.2139/ssrn.5336494 has been verified. The SSRN abstract page returned
HTTP 403. Their source-model and result comparison remains unverified.
These observations support no worldwide absence guarantee or priority claim.
