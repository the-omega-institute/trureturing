---
bibkey: puri2001arithmetic
authors: "Yash Puri and Thomas Ward"
year: 2001
title: "Arithmetic and growth of periodic orbits"
doi: null
url: "https://cs.uwaterloo.ca/journals/JIS/VOL4/WARD/short.tex"
claim: "Section 2, Exact realization, gives the divisor decomposition of periodic points, its Mobius inversion, and the criterion that each transformed count is nonnegative and divisible by its period. The converse uses disjoint cycles."
strata_touched:
  - D5/S1/Dynamics/PeriodicOrbits/OrbitCounting
  - D5/S1/Dynamics/PeriodicOrbits/FiniteRealization
license: citation-only
triage: anchor
---

# Periodic points and exact realization

The article appears in Journal of Integer Sequences 4, Article 01.2.1.
Section 2 decomposes points fixed at time n by their least positive periods.
Each orbit of least period n contains n distinct points. The lemma labelled
`exactrealization` characterizes exactly realizable nonnegative integer sequences
by nonnegative, n-divisible Mobius transforms.

The finite divisor-table version restricts all cycle lengths to divisors of a
fixed positive M. It constructs a permutation on exactly a(M) points whose Mth
power is the identity. Only values at divisors of M are prescribed. Singleton
cycles and the empty permutation are included; the resulting action need not
have order exactly M and need not be transitive. No transient-tree data are
reconstructed. The formal phase decomposition uses the actual forward cycles
of an arbitrary finite update, without an injectivity assumption.

## Verified locator

Source: https://cs.uwaterloo.ca/journals/JIS/VOL4/WARD/short.tex

Section 2, Exact realization: the equations labelled `sumoverdivisors`,
`basicmobiusinversion` and `divisibilitycondition`, followed by the lemma
labelled `exactrealization`. The preceding paragraph gives the disjoint-cycle
converse used by the finite divisor-table restriction.
