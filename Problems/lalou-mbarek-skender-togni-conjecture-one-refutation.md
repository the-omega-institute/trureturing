---
slug: lalou-mbarek-skender-togni-conjecture-one-refutation
bibkey: lalou2026completely
doi: 10.48550/arXiv.2512.15486
url: https://arxiv.org/abs/2512.15486v2
triage: theorem
motivation_gids:
  - D5/S3/ConceptDynamics/GraphColoring/AnnorCoverRefutation.annor_conjecture14_false
---

# Refutation of the panchromatic pairing conjecture

## Problem

Lalou, Mbarek, Skender, and Togni, *Completely Independent Spanning Trees in
Split Graphs: Structural Properties and Complexity*, arXiv:2512.15486v2,
Section 5, Conjecture 1 (verbatim apart from plain-text typography):

> Every hypergraph H satisfies
> chi_p^2(H) = chi_p(H) - ceil(alpha_{chi_p(H)}(H)/2).

Here chi_p and chi_p^2 are the maximum feasible panchromatic and
bipanchromatic color counts. A bipanchromatic coloring requires every global
color class to occur at least twice. The quantity alpha_k is the minimum number
of globally unique colors over all panchromatic k-colorings.

## Motivation

The published equality has a six-vertex counterexample with three four-element
edges and no isolated vertex. Formalizing the actual maxima and the minimum
over all maximizing colorings tests the precise extremal content rather than a
bounded surrogate or an assumed invariant value.

## Gap

The exact source statement, six-vertex witness, success and falsification
criteria, and bounded literature-status scope were preregistered in
[issue #8518](https://github.com/the-omega-institute/trureturing/issues/8518)
before the first Lean edit. A bounded screen of the primary and latest arXiv
records, arXiv results for bipanchromatic coloring, author and OpenAlex
records, the project library, pinned Mathlib, and public Lean keyword results
found no exact earlier resolution in the searched scope. Crossref records the
journal publication as *Discrete Applied Mathematics* 391 (2026), pages
511--522, DOI `10.1016/j.dam.2026.05.028`; publisher full text remains
unverified because access returned HTTP 403. No worldwide novelty or priority
claim is made.

## Route

Let the vertex type be Fin 6 and take edges `{0,1,2,3}`, `{0,1,2,4}`, and
`{0,1,2,5}`. Coloring the core by three distinct colors and all petals by a
fourth proves panchromatic feasibility at four. Any panchromatic coloring maps
the first four-element edge onto all colors, so its color count is at most four.

For an arbitrary panchromatic four-coloring, the first edge map is injective.
The other two edges force vertices 4 and 5 to have vertex 3's missing color.
Thus the three core color fibers are singletons in every maximizing coloring;
the displayed coloring attains exactly three singleton colors. Hence alpha_4
is three.

Color vertex v by v modulo three to obtain a bipanchromatic three-coloring.
For any bipanchromatic k-coloring, the k global fibers each have cardinality at
least two and their cardinalities sum to six, so k is at most three. Therefore
the extrema are chi_p=4, alpha_4=3, and chi_p^2=3, while the conjectured right
side is two.

## Falsifier

A defect in the refutation would be exposed by a panchromatic coloring using
more than four colors, a panchromatic four-coloring with fewer than three
singleton global fibers, or a bipanchromatic coloring using more than three
colors. Any mismatch between the finite-set definitions and the source's
global color multiplicities would also invalidate the result.

## Evidence

The 207-line Lean module
`D5/S3/ConceptDynamics/GraphColoring/PanchromaticPairingConjectureRefutation`
has exactly the public surface `claim : Prop` and `result : Not claim`. The
claim uses relational extrema with attainment and universal inequalities; the
result constructs all three witness certificates. Both declarations use only
the standard axiom closure `[propext, Classical.choice, Quot.sound]`. The
finite witness checks use kernel `decide`, not `native_decide`.

## Triage

`theorem`; resolution `refuted`. The public result has `proof_shape: content`:
its live proof constructs the source model, both universal maximum bounds, and
the all-optimal-coloring singleton lower bound. The public conclusion itself is
the escape witness. Its `admission_basis` is `open-problem-resolution`, and its
computational utility is the typed `certified-instance` refutation from
`result` to `claim`.

## ASSUMED-UNVERIFIED

The bounded source and literature search is not exhaustive coverage and does
not establish worldwide novelty or priority. The journal full text and any
unpublished answers to the conjecture remain unverified.
