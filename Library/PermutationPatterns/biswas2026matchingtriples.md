---
bibkey: biswas2026matchingtriples
authors: Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian
year: 2026
title: "Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples"
doi: 10.48550/arXiv.2609.08562
url: https://arxiv.org/abs/2609.08562v1
claim: "Classifies triples of patterns of length three up to shape-Wilf-equivalence and enumerates the perfect matchings avoiding each triple class except P1 = {123, 132, 213} and P13 = {132, 213, 321}; Section 6, Question 1 asks for these two enumerations."
strata_touched:
  - D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchings
  - D5/S3/Combinatorics/PatternMatchings/P13Correspondence
  - D5/S3/Combinatorics/PatternMatchings/P13Completions
  - D5/S3/Combinatorics/PatternMatchings/P13Counts
  - D5/S3/Combinatorics/PatternMatchings/P13Series
license: citation-only
triage: anchor
---

# Biswas, Shankar and Sivasubramanian, matchings avoiding triples of patterns

The paper classifies all triples of permutation patterns of length three up to shape-Wilf-equivalence on Ferrers
boards and, through the Bloom–Elizalde correspondence between Ferrers-board transversals and perfect matchings,
enumerates the perfect matchings of [2n] avoiding each class. In the matching setting three arcs form an occurrence
of a pattern only when their three left endpoints precede their three right endpoints; Section 4, Figure 1 fixes the
labels (321 is the crossing (1,4),(2,5),(3,6), 123 the nesting (1,6),(2,5),(3,4)). The enumeration remained open for
P1 = {123, 132, 213}, with counts 1, 3, 12, 55, 271, 1400, 7471, 40841, and for P13 = {132, 213, 321}; Section 6,
Question 1 asks for both.

The module `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchings` answers the P1 clause with the generating
function (1 − zH)/(1 − z − zH), H = Σ Cat_k F_{k+3} z^k.

The module `D5/S3/Combinatorics/PatternMatchings/P13Correspondence` proves the structural bridge for P13:
for every n ≥ 0, actual P13-avoiding perfect matchings of Fin(2n) are in bijection with complete general-rank scans
accepted by explicit normalized S/T transitions. Post-closure base survivors and pending openings are separate.
Source labels {132, 213, 321} correspond to chronological closing words {231, 312, 123}. The equivalence includes
empty and disconnected matchings. The companion modules `P13Completions` and `P13Counts` now prove finite
continuation carriers, a forced-prefix and first-closure decomposition, and the triangular recurrence
`P13Counts.c_triangular`; `P13Counts.actualCount_continuation` transfers this recurrence to the actual matching
carrier. These results do not yet give the explicit P13 generating function or a closed coefficient formula, so the
full enumeration part of Section 6, Question 1 remains open.

The companion module `D5/S3/Combinatorics/PatternMatchings/P13Series` proves `P13.completion_functional_equation`
for the concrete catalytic series `F(u,z) = Σ_{d≥0}(Σ_{m=0}^d c(m,d)u^m)z^d ∈ ℚ[u][[z]]`, where `c(m,d)` counts
literal completions from an old single block of size `m`: `u` marks that size and `z` marks the `d` future closures.
The proved support is `c(m,d)=0` for `m>d`, with `c(m,m)=1`, so `[z^d]F` has `u`-degree at most `d`. Its `u^0`
coefficient is `A(z)=Σ_{n≥0}c(0,n)z^n=Σ_{n≥0}actualCount(n)z^n`, the ordinary series for the original P13-avoiding
perfect matchings of `Fin(2n)`, including empty and disconnected matchings. The finite triangular recurrence yields
`(u-1-z*u^2)*F = u-(1+z*u^2)*A+z*u^2*F(1/(1-z*u),z)`; the transformed marker is evaluated coefficientwise on
finite polynomials, with each resulting `z` coefficient a finite sum. This proves the functional-equation step only:
it does not supply an explicit `G`, prove `A=G`, give a closed all-n coefficient formula, or complete P13/Question 1.

In Fatima Hessas’s thesis [On generating functions associated to patterns](https://dspace.ummto.dz/server/api/core/bitstreams/776a19a2-c9b8-4af6-898e-46fa091e1c59/content)
(academic year 2023/2024), the inspected Theorems 3.1–3.2 concern ordinary matchings avoiding the single pattern 312
or listed class-I pairs; Theorem 3.3 concerns set partitions. These theorem scopes do not provide an exact ordinary
matching triple theorem for P13 = {132, 213, 321}.

## Verified locator

DOI: 10.48550/arXiv.2609.08562

URL: https://arxiv.org/abs/2609.08562v1

- Locator: Section 4 and Figure 1 (matching patterns); Section 6, Question 1; Table 2 (reported counts).
- Formal locator: `D5/S3/Combinatorics/PatternMatchings/P13Series`, `P13.completion_functional_equation`.
