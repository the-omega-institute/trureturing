---
slug: loopy-generalized-degree-polynomial
bibkey: kirillov2026loopy
doi: null
url: https://arxiv.org/abs/2609.07728v1
triage: theorem
motivation_gids:
  - D5/S3/Factorization/Combinatorics/LoopyGeneralizedDegree.result
---

# The ordinary Loopy polynomial does not determine the generalized degree polynomial

## Problem

Problem 11.3 of `kirillov2026loopy` asks exactly:

> Does L_G determine the generalized degree polynomial GD_G?

The source's conventions admit every finite undirected multigraph, loops and
parallel edges included, and Problem 11.3 adds no restriction; the sentences
that follow it introduce the companion Problem 11.4 about degree sequences,
which Theorem 4.3 settles in the loopless case and Theorem 6.15 settles through
the refined polynomial. The pair delivered here carries loops and therefore
lies inside the problem's own domain.

In repository coordinates the target quantifies independently over finite
vertex sets `V W`, edge-occurrence lists `E F` and accumulated-loop functions
`ell eta`. From `Valid V E ell`, `Valid W F eta` and
`loopy V E ell = loopy W F eta` it concludes equality of the exponent-triple
multisets of the generalized degree polynomial. No looplessness, connectedness,
simplicity or equal-order hypothesis is present.

## Motivation

Display (6.10) of the source defines the generalized degree polynomial of Crew
as the sum over subsets S of the vertex set of q to the size of S, r to the
number of edges inside S, and t to the number of edges with exactly one
endpoint in S. A loop lies inside S exactly when its vertex does, and never
crosses. Two graphs share that polynomial exactly when the multisets of those
exponent triples agree, so the multiset is a faithful record of it.

The ordinary evaluator is already frozen here as
`D5/S3/Factorization/Combinatorics/LoopyEvaluator.loopy`, whose recursion
retains a contracted edge as a loop and merges the endpoint loop counts. The
companion Problem 11.4 was answered affirmatively at
`D5/S3/Factorization/Combinatorics/LoopyDegreeSequence.loopy_determines_degree_multiset`.
That answer is compatible with this one: the generalized degree polynomial
refines the degree sequence, so determining the coarser invariant says nothing
about the finer one.

## Gap

Nothing in the source settles the ordinary case with loops. Theorem 4.3 is
loopless, and Theorem 6.15 and Corollary 6.7 both run through the refined
polynomial. No printed example of the source substitutes into Problem 11.3 as
an answer.

## Route

Two trees on the vertices 0 through 7, one carrying a loop at vertex 1 and one
carrying a loop at vertex 4, are exhibited. Running the deletion-contraction
recursion to its 128 leaves on each gives one and the same polynomial of 25
monomials, so the hypothesis holds. Their exponent-triple multisets differ:
among the subsets of size two spanning two inside edges and two crossing edges
there is exactly one for the first graph and exactly two for the second, so the
conclusion fails.

Both graphs have degree multiset 1, 1, 1, 1, 2, 2, 3, 5, which is consistent
with the affirmative answer to Problem 11.4.

## Falsifier

Any pair of valid encodings with equal ordinary Loopy polynomials and equal
exponent-triple multisets leaves the endpoint untouched; the endpoint is
refuted only by showing that the exhibited pair does not have equal ordinary
Loopy polynomials, or that one of the two encodings is invalid, or that the
exponent triples of the two agree after all. Each of these is a finite check on
explicit data.

## Evidence

The endpoint is
`D5/S3/Factorization/Combinatorics/LoopyGeneralizedDegree.result`, proved
against the frozen evaluator of
`D5/S3/Factorization/Combinatorics/LoopyEvaluator`. Both hypotheses and the
separating computation are closed inside that one proof; no companion theorem
is introduced.

Eight vertices is the smallest order at which this occurs among trees carrying
a single loop. Orders three through seven were exhausted outside Lean: every
pair with a common ordinary Loopy polynomial there also has a common
exponent-triple multiset, the counts of Loopy classes being 2, 4, 9, 20 and 48.

The public preregistration is issue 8595 in `the-omega-institute/trureturing`.

## Triage

The public endpoint has `proof_shape: bind-only` and
`admission_basis: open-problem-resolution`. The settlement itself is the new
content: the source states Problem 11.3 as open and no literature check located
an answer, so the contribution is the verdict rather than the steps that reach
it. Its computation is a typed refutation certificate with
`kind=certified-instance` and `basis=refutes`.

## ASSUMED-UNVERIFIED

The minimality statement covers trees carrying exactly one loop. Graphs with
several loops, with multiple edges, or with cycles among the non-loop edges
were not enumerated, so no claim is made that eight vertices is minimal over
all graphs.
