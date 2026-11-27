---
bibkey: elder2026turnpike
authors: C. S. Elder, Guillaume Marçais, Carl Kingsford
year: 2026
title: "Turnpike with Uncertain Measurements: Triangle-Equality Integer Programming with a Deterministic Recovery Guarantee"
doi: 10.4230/LIPIcs.WABI.2026.20
url: https://drops.dagstuhl.de/storage/00lipics/lipics-vol390-wabi2026/html/LIPIcs.WABI.2026.20/LIPIcs.WABI.2026.20.html
claim: "Proposition 10 defines the guarded ordered-addition marginal system; System 11 relaxes P and T to the unit interval. Lemma 13 concerns scalar triangle equalities; Lemma 14 and Appendix A.3 give containment rank bounds."
strata_touched:
  - D5/S3/Combinatorics/Turnpike/SpineProjectionObstruction
  - D5/S3/Combinatorics/Turnpike/ContainmentRankBounds
license: CC-BY-4.0
triage: anchor
---

# Numerical triangle marginals

## Verified locator

DOI: https://doi.org/10.4230/LIPIcs.WABI.2026.20

URL: https://drops.dagstuhl.de/storage/00lipics/lipics-vol390-wabi2026/html/LIPIcs.WABI.2026.20/LIPIcs.WABI.2026.20.html

The published WABI 2026 article, Section 3.1, Proposition 10, System 11,
and Section 3.5 with Lemma 13 supply the numerical relation, marginal
constraints, relaxation, and scalar endpoint-spine comparison described below.
These locators attest the source model and scalar statement, not the
repository's fixed-assignment counterexample.

## Source semantics

Section 3.1 defines the ordered relation by exact numerical addition and the
repeated-label multiplicity guard. Proposition 10 requires row normalization,
label counts, triangle normalization and the three interval-label marginals.
System 11 retains those equalities with both arrays bounded between zero and
one. Section 3.5 states the endpoint-spine reduction after Lemma 13. The lemma
itself equates scalar triangle consistency with a coordinate-difference ruler.

The fixed-P projection comparison formalized here is an explicit interpretation
of the reduction sentence. The seven-point fractional obstruction is a
repository derivation. It does not contradict scalar Lemma 13, integral endpoint
reconstruction, or feasibility with the assignment array free. That fixed-assignment result does not address containment-pruned formulations
or LP integrality. Dissertation Chapter 4
has not been checked as a supplier for this comparison.

## Containment rank bounds

The published Section 3.5, Lemma 14 and Appendix A.3 bound the rank of
every interval difference using its superintervals and subintervals. The
corresponding arXiv:2603.18283v1 statement is Lemma 13 with an inline proof.
The source defines rank as any occurrence position in the expanded decreasing
distance multiset, so its bounds apply to both endpoints of a repeated-value
block.

For zero-based endpoints i < j in an n-point increasing real ruler, the lower
rank bound is (i+1)(n-j) and the upper bound is
choose(n,2)-choose(j-i+1,2)+1. The formalization retains the original real
realization and histogram predicates. Its histogram bridge permits empty
unused bins, including negative unused labels; a used label has positive
multiplicity because its interval fiber is inhabited. These bounds justify
the original rank-block intersection mask. They do not imply LP integrality
or sufficiency of local marginals.
