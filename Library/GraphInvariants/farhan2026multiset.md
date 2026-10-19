---
bibkey: farhan2026multiset
authors: Mohammad Farhan, Sandi Klavžar, Dorota Kuziak, Ismael G. Yero
year: 2026
title: "Multiset resolvability parameters in graphs: A survey with new results and open problems"
doi: null
url: https://arxiv.org/pdf/2607.10311v1
claim: "Section 6.1 defines edge multiset resolution using minimum shortest endpoint distances; Problem 24 asks whether every once-subdivided complete graph of order at least three has infinite edge multiset dimension."
strata_touched:
  - D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionResolution
license: citation-only
triage: anchor
---

# Edge multiset resolution of once-subdivided complete graphs

## Verified locator

URL: https://arxiv.org/pdf/2607.10311v1

Problem 24, section 7.4, printed page 27: “Is it true that edim_m(K_n^1) = infinity for every integer n >= 3?”
Printed page 21 defines K_n^k by inserting exactly k vertices into each edge of K_n.
Section 6.1, printed page 20, defines the distance from a vertex to an edge as the minimum
of its two shortest endpoint distances. A resolving landmark set distinguishes every pair
of graph edges by the multiset of these distances, including multiplicity. Its nonexistence
means infinite edge multiset dimension.

The native result treats every n at least three and every subset of both vertex classes.
Its graph is the incidence subdivision of the complete graph, with a midpoint for each
unordered pair of distinct originals. Reachability and all shortest-distance formulas are
proved; the final statement uses actual graph adjacency and actual shortest distances.

The survey credits its reference [29], Ikhlaq, Ismail, Siddiqui and Nadeem,
“A new technique to uniquely identify the edges of a graph,” Symmetry 15 (2023), article 762,
for the parameter and earlier results. This attribution is through the survey; direct access
to that article returned HTTP 403. The survey's Lemma 6.3 covers the n=3 instance but does
not supply the all-n result, since disjoint midpoint-to-edge distances equal three for n at
least four. Binary row sums, symmetry, finite permutations, pigeonhole counting and
complement counting are classical ingredients; no originality is claimed for them.

## Literature scope

The versioned source explicitly lists Problem 24 as open. The inspected arXiv:2608.09983v1
concerns the distinct hypercube question, and the inspected section 7.4 of
arXiv:2607.08128v1 supplies no resolution of this once-subdivided complete-graph family.
The released repository's graph modules, problem dossiers and literature notes contained
no matching native result in the bounded candidate search. These checks support source
attribution and bounded overlap only; worldwide current openness and priority are
ASSUMED-UNVERIFIED.
