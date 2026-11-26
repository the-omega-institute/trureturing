---
slug: froese-george-2026-path-cover-rank-question-1
bibkey: froesegeorge2026pathcovers
doi: 10.48550/arXiv.2610.20890
url: https://arxiv.org/abs/2610.20890v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Lattices/FroeseGeorgePathCoverRankRefutation.result
---

# Froese–George Question 1 on path-cover ranks

## Problem

Matteus Froese and Ian George, *Path Covering Spaces of Posets*, arXiv:2610.20890v1, §4, p. 23, ask:

> Is the sequence $(r_k)_k$ where $r_k$ is the number of elements of rank $k$ in the lattice of path covers always log-concave or unimodal?

The proposition ranges over finite partial orders with a least element. The lattice elements are compatible families of partitions of all saturated paths from the least element, with a partition at every endpoint and a length-zero path at the least element. Along each base Hasse edge, extension takes each source block into one target block. Order these families from coarser to finer. The rank is the sum over endpoints of the number of blocks minus one. The height $H$ is the sum of the number of paths minus one. The predicates are $r_{k-1}r_{k+1}\le r_k^2$ for every $0<k<H$, and the existence of a mode $m\in[0,H]$ with weak increase through $m$ and weak decrease thereafter. [Versioned question](https://arxiv.org/html/2610.20890v1#Thmquest1)

## Motivation

Theorem 3 establishes supersolvability of the intended path-cover lattice. Question 1 asks about its rank sizes. A strict valley in a distributive example shows that this additional structure still permits a failure of both predicates.

## Gap

The source model used here is the rooted lattice of Definition 2 and Theorems 1 and 2, with rank and height from Corollary 1. Bare Definition 1 permits a singleton over the top of a two-element chain. For the sole point of the domain, the count identity compares the length-zero path at the top and the absence of a path from the top to the bottom. Requiring the root to map to the least element yields the intended maps over the base. Hasse edges lift uniquely, and partition blocks group rooted paths whose lifts end at the same point. Conversely, the extension edges between endpoint-tagged blocks give the cover, with comparison maps over the base corresponding to componentwise refinement. The formal claim directly quantifies over the compatible endpoint partitions in Definition 2. The count-map correspondence here applies to root-preserving maps between rooted finite posets and is given in prose.

Proposition 6 supplies a product decomposition when bases are joined under a new root. Proposition 7 gives the reduction to the region with multiple rooted paths, together with its path multiplicities. Remark 4 uses these results to express the lattice of a minimally splitting base as the product of the downset lattices of its branches. [Proposition 6](https://arxiv.org/html/2610.20890v1#Thmpp6) · [Proposition 7](https://arxiv.org/html/2610.20890v1#Thmpp7) · [Remark 4](https://arxiv.org/html/2610.20890v1#Thmrk4)

A bounded literature screen covered the versioned source, Hoffman's cited predecessor, public citation indexes, and the project and Mathlib catalogs. It found no exact prior answer in that scope. [Froese–George](https://arxiv.org/abs/2610.20890v1) · [Hoffman](https://doi.org/10.37236/1576) · [Issue #33328](https://github.com/the-omega-institute/trureturing/issues/33328)

## Route

Take a root covered by two incomparable vertices. Each of those two vertices is covered by the first vertex of each of two disjoint branches. Each branch consists of a three-vertex stem followed by three leaves covering the last stem vertex. The displayed edges give the Hasse diagram of a 15-element poset.

The path at each endpoint is a Mathlib quiver path from the least element with one arrow for each Hasse cover. There is one saturated rooted path to each of the initial three vertices and two to each branch vertex, distinguished by the first step. Extension within a branch preserves this label. At a two-path vertex there is a merged partition and a discrete partition. If the successor is split, the predecessor must be split too, since extension of a merged block would meet two successor blocks. All other combinations are allowed, and extension from a one-path vertex gives no restriction. The split vertices form an arbitrary lower ideal of each branch. The inverse assigns the discrete partition at ideal vertices and the merged partition elsewhere. Inclusion of the two ideals gives exactly the coarser-to-finer order, and total ideal size gives the source rank.

In one branch, an ideal missing the last stem vertex is an initial stem segment of size zero, one or two. An ideal containing that vertex contains the full stem and an arbitrary subset of the three leaves. The one-branch rank polynomial is $1+t+t^2+t^3(1+t)^3$. The product of the independent branch polynomials gives height $12$ and coefficients $15,14,17$ at degrees $6,7,8$.

## Falsifier

The certificate depends on the Hasse edges giving exactly the claimed path labels, compatible families being in bijection with the two ideals, and the bijection preserving refinement and source rank. With these facts, the two strict comparisons $r_6>r_7<r_8$ rule out a mode anywhere in the valid interval, and $r_7^2=196<255=r_6r_8$ violates log-concavity at an interior rank.

## Evidence

The Lean declaration `D5.S3.Combinatorics.Lattices.FroeseGeorgePathCoverRankRefutation.result` proves the literal negation `¬ claim`. `Branch.idealEquiv` is the order isomorphism on the full compatible-family type. `Branch.rankFiberEquiv` identifies the source fiber at each natural rank with the fiber of the sum of the two cardinalities. Kernel-reduced finite enumeration on the latter gives the three source counts in `Branch.witness_rank_counts`.

Froese and George posed the question and supplied the lattice, grading and structural product pattern. The Codex CLI successor-search seat supplied the particular 15-element base and its strict rank valley. The source-qualification seat independently derived the three counts for that base. The Codex CLI formal probe supplied the original Lean proof, which checks the concrete realization of the product and the rank computation. The paper is cited under its arXiv distribution terms. [Issue #33328](https://github.com/the-omega-institute/trureturing/issues/33328) · [Source license](https://arxiv.org/licenses/nonexclusive-distrib/1.0/)

## Triage

Tier 1. The designated refutation supplies a certified instance for the preregistered external open problem. Its use is the literal refutation of the closed proposition. The designated result is exempt from four-slot escape registration under CLAUDE.md §3.9. [Preregistration](https://github.com/the-omega-institute/trureturing/issues/33328)

### What the settlement shows

- **Proved and computed for the witness.** At most two rooted paths per vertex still permits a strict valley. `Vertex.pathEquiv` gives singleton or Boolean endpoint fibers, `Branch.idealEquiv_preserves_rank` gives the total ideal size as the source rank, and `Branch.witness_rank_counts` computes $15,14,17$. The strict inequalities and $196<255$ rule out both predicates on the same base in `result`.
- **Proved for the one-path case by the partition definition.** If every endpoint has exactly one rooted path, each partition has one block. The unique family is compatible because each singleton block extends into the unique block at the next endpoint. It has rank zero, the height is zero, and $r_0=1$. The log-concavity test has no interior index, and $m=0$ is a weak mode.
- **Proved in the source for the rooted lattice.** Theorem 2 gives the lattice, Corollary 1 gives its rank and height, and Theorem 3 gives supersolvability. These results apply to the witness. The counterexample shows that the rank sizes of a supersolvable lattice of this form can fail both shape predicates. [Theorem 2](https://arxiv.org/html/2610.20890v1#Thmtm2) · [Corollary 1](https://arxiv.org/html/2610.20890v1#Thmcor1) · [Theorem 3](https://arxiv.org/html/2610.20890v1#Thmtm3)

## ASSUMED-UNVERIFIED

Exhaustive literature coverage, publication priority, and minimal size of a base poset exhibiting both failures are unverified. The Lean certificate concerns the rooted partition lattice of Definition 2. The count-map correspondence in Gap is a prose argument.
