---
bibkey: tsaban2003permutation
authors: Boaz Tsaban
year: 2003
title: "Permutation graphs, fast forward permutations, and sampling the cycle structure of a permutation"
doi: 10.1016/S0196-6774(03)00017-8
claim: "Acyclic partial permutation graphs have path components with unique endpoints, exactly (m-1)! full-cycle extensions for m components, and a uniform choice of the next component among the other components."
strata_touched:
  - D5/S3/Combinatorics/Graph/LinearForests/DirectedForestCompletion
license: citation-only
triage: anchor
---

# Partial permutation graphs and full-cycle extensions

## Verified locator

DOI: 10.1016/S0196-6774(03)00017-8

Journal of Algorithms 47 (2003), 104–121. Section 1, Lemmas 1.1–1.3,
Definition 1.4 and Lemma 1.5, pages 107–109.

## Mathematical scope

The source works on the full labelled carrier V = {0,...,N-1}. Its components
are the connected components after forgetting edge directions, explicitly
including isolated vertices. Lemma 1.1 identifies acyclic partial permutation
graphs with proper partial cyclus graphs and gives a unique minimum and maximum
in each component. Lemma 1.2 constructs every full-cycle extension by connecting
component maxima to component minima according to a cycle of the components;
the converse recovers that component cycle. It counts exactly (m-1)! extensions.
Lemma 1.3 describes the effect of adding an endpoint edge.

Definition 1.4 specifies the uniform full-cycle oracle and an oracle choosing
uniformly among components other than the queried component. Lemma 1.5 proves
their finite nonrepeating consistent-answer probabilities equal, using the
extension count. Its proof on page 109 gives probability 1/(N-j-1) for each
remaining component at a stage with N-j components.

The Lean module expresses this classical component contraction on an arbitrary
finite labelled type, retaining the original relation E and actual full-cycle
permutations. Its endpoint-compatible equivalence gives the exhaustive
completion count. Its PMF formulation conditions the uniform law on extending
E, pushes that same completion law to component cycles, and evaluates the raw
endpoint event under the same law: zero for the same component and 1/(m-1)
for a different component, for m at least two. These formal interfaces make
explicit the correspondence to the classical construction and uniform law;
no literature priority is claimed.

This note supplies mathematical provenance. The compiled Lean suppliers and
their licenses are separate: Mathlib, leanprover/cslib, and the adapted
full-support correspondence documented in
[the Liu–Ye license note](liuye2026cyclesupport.md). Neither the present Lean
statement nor this citation establishes an adaptive transcript theorem,
random-label conditioning, an undirected orientation multiplicity, an
alternating-cycle law, a query bound, or an EXIT probability.
