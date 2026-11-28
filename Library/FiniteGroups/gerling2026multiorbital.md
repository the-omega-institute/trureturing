---
bibkey: gerling2026multiorbital
authors: Melanie Gerling
year: 2026
title: "The Multiorbital Bivariate Chromatic Polynomial: A Subgroup-Lattice Refinement"
doi: null
url: https://arxiv.org/html/2609.01866v5
claim: "The conclusion asks whether the multiorbital bivariate chromatic polynomial is a complete invariant for graph actions."
strata_touched:
  - D5/S3/Combinatorics/Graph/Chromatic/GerlingMultiorbitalCompletenessRefutation
license: citation-only
triage: anchor
---

# Multiorbital completeness for graph actions

## Verified locator

[arXiv:2609.01866v5](https://arxiv.org/html/2609.01866v5). Section 2.1
defines generalized proper colorings for integer palettes with
\(0 \le y \le x\). Section 2.2 gives the cycle quotient convention
and the fixed-coloring interpretation of its polynomial. Section 3
defines the multiorbital polynomial as the sum of the orbital
polynomials over all subgroups of the acting group.

## Completeness question

The conclusion asks whether there are nonisomorphic graph actions
on the same finite acting group with identical multiorbital
polynomials. The formalized collision concerns the restriction to
connected graphs carrying faithful actions of the cyclic group of
order two, with polynomial equality and no action isomorphism.

The separate implication question asks whether multiorbital equality
implies orbital equality. The counterexample to completeness has equal
orbital polynomials as well. [Issue #24209](https://github.com/the-omega-institute/trureturing/issues/24209)

## Literature scope

Dohmen, Pönitz and Tittmann exhibit bivariate chromatic collisions in
Section 6, page 81, Figure 6. For the faithful trivial acting group the multiorbital
invariant is the bivariate chromatic polynomial, so those collisions
already refute unrestricted completeness, as observed in issue #21295.
The connected, faithful order-two collision has equal bivariate
polynomials both for the original graphs and for their nonidentity
cycle quotients. Priority for this restricted statement remains unverified.
[Dohmen, Pönitz and Tittmann (2003)](https://doi.org/10.46298/dmtcs.335) ·
[Issue #21295](https://github.com/the-omega-institute/trureturing/issues/21295#issuecomment-6391235009) ·
[Issue #35029](https://github.com/the-omega-institute/trureturing/issues/35029)
