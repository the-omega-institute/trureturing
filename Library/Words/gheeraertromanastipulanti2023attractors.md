---
bibkey: gheeraertromanastipulanti2023attractors
authors: France Gheeraert, Giuseppe Romana, Manon Stipulanti
year: 2023
title: String attractors of some simple-Parry automatic sequences
doi: null
url: https://arxiv.org/abs/2302.13647v2
claim: Conjecture 42 gives the minimum string-attractor size of every original fixed-point prefix under weak cyclic maximality.
strata_touched:
  - D5/S1/Words/Attractors/FiniteWordAttractors
  - D5/S1/Words/Attractors/PeriodicPrefixAttractors
  - D5/S1/Words/Attractors/CyclicMorphismAttractorMinimum
license: citation-only
triage: anchor
---

# String attractors of some simple-Parry automatic sequences

Definition 2 supplies the original substitution, its iterates and their lengths.
The unnumbered definition opening Section 4 supplies unrestricted string
attractors. Paper positions are one-based; each paper position is the Lean
zero-based position plus one, preserving cardinality and occurrence intersection.
The working hypotheses fix k >= 2, nonnegative integer coefficients with positive first and last
entries, and the original substitution on k letters. Conjecture 42 concerns
every positive prefix length when the coefficient word with its last entry
decreased by one is a weak lexicographic maximum of its cyclic rotations.

Proposition 4 supplies the original short and full block recurrences.
Lemma 22 and Theorem 23 describe canonical endpoint-attractor intervals;
Proposition 34 connects cyclic maximality with fractional prefixes. These
published statements supply context, not premises of the Lean proof.

The formal proof uses a direct periodic-digit/interior induction and a scan
through all k original blocks. The chosen cap U(n+1)-1 is a proved periodic
prefix; it is not identified with a source maximal fractional exponent.
The proof retains equal rotations, proper powers, unary primitive roots,
allowed zero coefficients and every original prefix length.

The formalization reuses morphismPower, wordPower and pinned Mathlib list and
finite-set APIs. No priority or worldwide novelty claim is made.

The bibkey and year refer to the initial 2023 arXiv submission. The source
used here is v2, dated 22 March 2024, licensed under CC BY 4.0. This Library
note uses citation-only attribution; no external Lean implementation is copied.
