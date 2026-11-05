---
bibkey: ahanjidehekimyildiz2022matching
authors: M. Ahanjideh; T. Ekim; M. A. Yıldız
year: 2022
title: Maximum size of a triangle-free graph with bounded maximum degree and matching number
doi: 10.1007/s10878-024-01123-z
url: https://arxiv.org/abs/2207.02271v1
claim: Conjecture 6.5 states that Z(d) = floor(5(d+1)/4) for every odd d at least 21.
strata_touched:
  - D5/S3/Combinatorics/Graph/ComponentPacking/AhanjidehEkimYildizZ
license: citation-only
triage: anchor
---

# Maximum size of a triangle-free graph with bounded maximum degree and matching number

## Verified locator

DOI: 10.1007/s10878-024-01123-z

Source: https://arxiv.org/abs/2207.02271v1

The quotations and page numbers refer to arXiv version 1. The journal version is
identified by the DOI; its full text has not been independently verified here.

## Source statements

Section 2, page 3: “if d(w) = d − 1 for some w ∈ V(G) and d(v) = d for all
v ∈ V(G) − w, then G is said to be almost d-regular.”

Section 2, page 4: “A graph G is said to be factor-critical if G \\ v has a perfect
matching for all v ∈ V(G).”

Definition 4.2, page 8: “For any d ≥ 2, let Z(d) be the smallest natural number n
such that there exists a d-regular (if d is even) or almost d-regular (if d is odd)
triangle-free and factor-critical graph G with ν(G) = n.”

Proposition 4.3, page 8: “The graph Bd in Figure 2 is (almost) d-regular, triangle-free, and
factor-critical.” For odd d, the proposition gives ν(Bd) = ⌊5(d + 1)/4⌋
and |V(Bd)| = 2ν(Bd) + 1.

Conjecture 6.5, page 20: “For d ≥ 21 and odd, we have Z(d) = ⌊5(d + 1)/4⌋.”

## Encoding

Finite simple graphs are represented on `Fin n`. Almost regularity has a distinguished
vertex of degree `d-1`, and all other vertices have degree `d`. Factor-criticality
quantifies perfect subgraph matchings after each vertex deletion. The matching
number is the existing `DimerVirialFourthDifferenceRefutation.matchingNumber`.
The least admissible matching number is a natural-number infimum; natural division
in the conjecture is the displayed floor.

## Literature boundary

The preregistration is https://github.com/the-omega-institute/trureturing/issues/19633.
Its literature screen includes Banak–Ekim–Taşkın, arXiv:2304.01729v1, and the source's
journal locator. Completeness of the screen is ASSUMED-UNVERIFIED.

## Dense triangle-free prerequisite

The pentagon homomorphism theorem used here is the classical strict
three-eighths minimum-degree theorem of Roland Häggkvist,
“Odd Cycles of Specified Length in Non-Bipartite Graphs”,
North-Holland Mathematics Studies (1982), pages 89–99,
DOI 10.1016/S0304-0208(08)73552-7. It states that a finite triangle-free graph
with minimum degree greater than three-eighths of its order is homomorphic
to the five-cycle. The formal statement includes bipartite graphs.
The construction of the homomorphism is proved from finite graph counting.
The original chapter locator is identified bibliographically; its full text
has not been independently verified here.
