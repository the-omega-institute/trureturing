---
bibkey: gervacio2026identityseidel
authors: Severino V. Gervacio
year: 2026
title: On identity Seidel switches
doi: null
url: https://arxiv.org/abs/2601.04530v1
claim: "Problem 6.1 asks for a complete characterization of finite nonempty simple graphs in which every vertex is a vertex-ISS."
strata_touched:
  - D5/S3/Combinatorics/Graph/SeidelSwitching/VertexIdentitySwitches
license: citation-only
triage: anchor
---

# Gervacio, identity Seidel switches

## Verified locator

DOI: null

Source: https://arxiv.org/abs/2601.04530v1

Section 2, page 3, defines graphs and the vertex switch. Section 2.2, Theorem 2.6,
page 6 (source label `thm:subset-switch`), gives switching across an arbitrary subset.
Section 4, Definition 4.1, page 8, defines ISS; page 9 defines vertex-ISS and states
Lemma 4.4. Section 6, Problem 6.1, page 13, asks the characterization question.
Crossref title search for "On identity Seidel switches" returns no matching work.

## Source definitions

Section 2, page 3:

> Throughout, a graph G is an ordered pair G = ⟨V(G), E(G)⟩ where V(G) is a non-empty finite set whose elements are called vertices and E(G) is a set of 2-element subsets of V(G) called edges.

Section 2.1, page 3:

> Let G be a graph and v ∈ V(G). The Seidel switch of G by v, denoted v(G), is the graph obtained from G by deleting all edges vy where y ∈ N_G(v) and adding all edges vz where z ∈ V(G) ∖ N_G(v) and z ≠ v. In other words, we complement the adjacency relation between v and the rest of the vertex set, while leaving all other adjacencies unchanged.

Theorem 2.6, page 6:

> Let G be a graph and S a non-empty subset of V(G). Then S(G) is obtained from G by deleting all edges xy with x ∈ S and y ∈ V(G) ∖ S, and adding all non-edges xy with x ∈ S and y ∈ V(G) ∖ S. Edges with both ends in S or both ends in V(G) ∖ S remain unchanged.

Definition 4.1, page 8:

> Let G be a graph. A subset S ⊆ V(G) is called an identity Seidel switch (abbreviated ISS) if S(G) ≅ G.

Section 4, page 9:

> We say that {x} is a vertex-ISS if {x} is an ISS, and that {x, y} is an edge-ISS if {x, y} is an ISS and xy ∈ E(G).

## Problem

Problem 6.1, page 13:

> Characterize graphs G for which every vertex is a vertex-ISS. Lemma 4.4 gives a necessary condition in terms of the minimum and maximum degree; can this be strengthened to a complete characterization?

The characterization is exactly graph order one. The module proves this using edge-count
preservation and the degree change of the other vertices under a singleton switch.

Lemma 4.4, page 9, says that under the same hypothesis every minimum-degree vertex is
adjacent to every maximum-degree vertex. The characterization leaves only the one-vertex
graph. Its sole vertex is both minimum- and maximum-degree and has no loop, so the lemma's
literal conclusion requires a distinct-vertices convention or an order-at-least-two restriction.
Problems 6.2–6.4 concern the ISS group, automorphisms, and signed or weighted extensions.
