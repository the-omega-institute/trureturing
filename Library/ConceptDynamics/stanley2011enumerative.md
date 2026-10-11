---
bibkey: stanley2011enumerative
authors: Richard P. Stanley
year: 2011
title: Enumerative Combinatorics, Volume 1, second edition
doi: null
url: https://math.mit.edu/~rstan/ec/ec1.pdf
claim: "Section 1.9 gives B3=5; Example 3.10.4 defines the partition lattice ordered by refinement and its meet by nonempty block intersections."
strata_touched: []
license: citation-only
triage: anchor
---

# Finite partitions and refinement

The author-hosted version is dated 15 July 2011. Its PDF SHA256 is
`f669d7b0d78730b7c812794a437fb6a78e0c182c10dfd520bc26d627cf45a1d5`.
Page numbers below are printed page numbers for that version.

Section 1.9, p. 82, defines the Bell numbers by partitions of a finite set
into nonempty disjoint blocks and gives $B_3=5$. Example 3.10.4, p. 318,
and Figure 3.20 use refinement: $\pi\le\sigma$ means every block of $\pi$
lies in a block of $\sigma$. The discrete partition is the bottom and the
one-block partition is the top. The meet consists of the nonempty
intersections of blocks; the join is the least common coarsening.

[Section 27 of the static-seams continuation](../../docs/develop/theory/AURIC_FIB_ATOM_STATIC_SEAMS_TRANSITION_CIRCULATION_AND_FIBONACCI_TOGGLE_CYCLES.md)
uses these definitions to compare support inclusion and a supplied
single-toggle action with refinement and a partition join. Stanley supplies
the partition order, not the FIB observation or action contract.
