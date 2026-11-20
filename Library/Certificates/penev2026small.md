---
bibkey: penev2026small
authors: Irena Penev, Maya Stein, and Ana Trujillo-Negrete
year: 2026
title: "Small q-kernels in digraphs"
doi: 10.48550/arXiv.2608.00825
url: https://arxiv.org/abs/2608.00825v1
claim: "The authors ask whether the small q-kernel bound in Theorem 1.6 also holds for even q."
strata_touched:
  - D5/S3/ConceptDynamics/GraphColoring/GraphCoverDomination.IsDominating
license: citation-only
triage: anchor
---

# Small q-kernels in digraphs

## Verified locator

DOI: 10.48550/arXiv.2608.00825

URL: https://arxiv.org/abs/2608.00825v1

The versioned preprint is arXiv:2608.00825v1, dated 1 August 2026.
The authors pose the following question immediately after Theorem 1.6.

> We do not know whether Theorem 1.6 also holds if $q$ is even.

[Versioned abstract](https://arxiv.org/abs/2608.00825v1) · [Exact question](https://arxiv.org/html/2608.00825v1#S1.p12.1)

## Definitions and scope

A $q$-kernel is an independent set that reaches every vertex by a
directed path of length at most $q$, counting arcs and allowing length
zero. Section 2 uses a loopless digraph with at most one arc in each
ordered direction and permits both opposite arcs. Its underlying simple
graph joins vertices if either arc exists. An out-branching is a spanning
out-arborescence. Source-freeness means each vertex has an in-neighbor.
[Introduction](https://arxiv.org/html/2608.00825v1#S1) · [Preliminaries](https://arxiv.org/html/2608.00825v1#S2)

Theorem 1.6 proves the bound $|Q|\le |V(D)|/(q+1)+1$ for every odd
integer $q\ge3$ on source-free bipartite digraphs with an out-branching.
In the proof, the even modulus $q+1$ makes each depth residue lie in one
bipartition class. At even radius $q\ge4$, the theorem at $q-1$ still
gives the bound $|V(D)|/q+1$ for a $q$-kernel.
[Theorem 1.6](https://arxiv.org/html/2608.00825v1#S1.Thmtheorem6) · [Proof](https://arxiv.org/html/2608.00825v1#S5)

The Tier 1 preregistration preserves the printed lower endpoint by taking
even naturals $q\ge4$. It uses $(q+1)|Q|\le |V(D)|+q+1$ on all finite
digraphs satisfying the stated hypotheses. The fixed $q=4$ witness also
applies if the printed question is read to include radius two.
[Preregistration #31451](https://github.com/the-omega-institute/trureturing/issues/31451)

## Counterexample mechanism

The counterexample uses a directed six-cycle with one arc to a hub,
outward branches of lengths four, nine, and nine, and two return arcs
to the hub from depth five on the long branches. The 29 vertices and
31 arcs are specified in the problem dossier. The cycle forces two
centers because no outside vertex reaches it and no one center covers
all six cycle vertices. If the hub is absent, five disjoint predecessor
intervals force five off-cycle centers. If it is present, each return
arc bars the sole center that could cover two required vertices of its
long branch together. Each long branch then requires two centers, giving
five off-cycle centers including the hub. The witness needs seven
centers and the source bound allows six.

The quoted question, definitions, and odd-radius theorem are due to
Penev, Stein, and Trujillo-Negrete. The counterexample and its interval
argument come from the research for #31451. The Lean proof verifies the
complete refutation through the fixed radius-four witness.
[Problem dossier](../../Problems/penev-stein-trujillo-negrete-2026-even-q-kernel.md) · [Research issue](https://github.com/the-omega-institute/trureturing/issues/31451)

## Literature scope

The preregistration records two source screens against the submitted
version, accessible later literature, project records, and pinned
repository sources at `532d4d86f1b1f614b1653aab838d27d0ee3f0f41`. A
subsequent general counterexample with an odd directed cycle lies
outside the bipartite class. The cited radius-two unicyclic result
has narrower hypotheses. The reported search found no resolution in
the checked material. Coverage of unpublished or unindexed work and of
the full Wang–Deng–Chen text remains unverified.
[Preregistration and scope](https://github.com/the-omega-institute/trureturing/issues/31451) · [General counterexamples](https://arxiv.org/abs/2608.16977v1) · [Unicyclic bound](https://arxiv.org/abs/2307.04112v3)
