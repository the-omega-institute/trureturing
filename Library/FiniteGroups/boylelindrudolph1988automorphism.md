---
bibkey: boylelindrudolph1988automorphism
authors: Mike Boyle, Douglas Lind and Daniel Rudolph
year: 1988
title: The automorphism group of a shift of finite type
doi: 10.1090/S0002-9947-1988-0927684-2
url: https://www.math.washington.edu/~lind/Papers/AutomorphismGroupSFT.pdf
claim: Simultaneous guarded data-word permutations define finite permutation actions when full and partial marker overlaps are excluded.
strata_touched:
  - D5/S3/ConceptDynamics/Coding/MarkerPermutationAction
  - D5/S3/ConceptDynamics/Coding/ResetHistoryKernel
license: citation-only
triage: anchor
---

# Marker permutations in shifts of finite type

Mike Boyle, Douglas Lind and Daniel Rudolph, *The automorphism group of a shift
of finite type*, Transactions of the American Mathematical Society **306**
(1988), 71–114. DOI: [10.1090/S0002-9947-1988-0927684-2](https://doi.org/10.1090/S0002-9947-1988-0927684-2).

Primary text: [author-hosted PDF](https://www.math.washington.edu/~lind/Papers/AutomorphismGroupSFT.pdf),
section 2, printed pp. 74–75. The section constructs permutations of data words
between common markers by simultaneous replacement and excludes full and partial
marker overlaps. This construction is classical, not a publication novelty claim.

The repository development `MarkerPermutationAction` proves guard protection on
arbitrary bilateral original-edge sequences from edge unborderedness and a marker
longer than the data. It discharges legality, endpoints and injectivity on the
actual numbered ResetGraph, using the loops A=ab and B=acd. It does not assume a
full-shift conjugacy or a supplied marker automorphism. Extra edges and noncoded
exterior tails remain in the history domain.

`ResetHistoryKernel` connects this action to the original beam-image representation:
its image commutes with forward time, and the existing native cyclic polynomial
chart makes that image abelian. Alternating restrictions of the faithful symmetric
actions therefore land in the original representation kernel. Three-cycles are
commutators in the symmetric group, so the argument includes A4 without assuming
A4 perfect. This arithmetic bridge is a repository application; no theorem about
all marker permutations being inert is used as a premise.

The resulting family supplies nonabelian finite subgroups of unbounded orders.
It neither classifies the entire kernel nor establishes compatibility or nesting
of the subgroups for different data lengths.
