---
slug: loopy-degree-sequence-with-loops
bibkey: kirillov2026loopy
doi: null
url: https://arxiv.org/abs/2609.07728v1
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Witt/PrimitiveEulerLedger
---

# Degree recovery from the ordinary Loopy polynomial with loops

## Problem

Problem 11.4 of `kirillov2026loopy` asks exactly:

> Does L_G determine the degree sequence of an arbitrary graph G, loops included?

In repository coordinates, the complete target quantifies independently over
finite vertex sets `V W`, edge-occurrence lists `E F`, and accumulated-loop
functions `ell eta`. From `Valid V E ell`, `Valid W F eta`, and
`loopy V E ell = loopy W F eta`, it concludes
`degreeMultiset V E ell = degreeMultiset W F eta`. It assumes no equality of
orders. Lists preserve parallel occurrences; both endpoints of a pending loop
are counted, accumulated loops contribute twice, and mapping all vertices in
the carrier includes isolates. No connectedness, nonemptiness or simplicity
hypothesis is present.

## Motivation

Definition 1.1 and Proposition 2.1 supply the ordinary Loopy recursion and
choice independence. Section 6.5 supplies refined-degree context only. Neither
the source paper nor that section supplies the substitution x_r=[2r+1] or the
looped degree-recovery conclusion. The public preregistration is issue 8149 in
`the-omega-institute/trureturing`.

## Gap

The source laws and the frozen uniqueness theorem do not by themselves supply
the specialization that exposes every degree, the recovery of the common
order, or the exact finite coefficient transport. Those live steps are the
escape content required to pass from ordinary Loopy equality to all degree
counts, including count at degree zero.

## Route

The endpoint keeps two graph inductions live inside its proof and applies them
to both inputs. The degree specialization gives
`P = product_v [degree(v)+1]`. The order specialization is monic of degree the
carrier cardinality, so equality of ordinary Loopy polynomials first gives a
common order `n`; no order equality is assumed. Multiplication by `(1-t)^n`
then gives one common polynomial
`q = product_v (1-t^(degree(v)+1))`.

For a degree multiset `D`, set `c(r) = -Int.ofNat(D.count r)`. The finite
Euler representation at coefficient `k <= N` splits `D` using the actual
predicate `d < N`. Every omitted `d` satisfies `k < d+1`, so its factor cannot
change that coefficient. This includes the boundary `N=k=0`; it is not a
truncation shortcut. The frozen primitive Euler-ledger uniqueness result makes
the two count functions equal. Coordinate `r=0`, whose shifted factor is
`1-t`, recovers isolates.

## Evidence

`D5/S3/Factorization/Combinatorics/LoopyEvaluator.loopy_spec` owns the seven
representation and recursion laws. Although its Lean namespace is shared, its
source-module handle remains the evaluator module. The endpoint is
`D5/S3/Factorization/Combinatorics/LoopyDegreeSequence.loopy_determines_degree_multiset`.
Its Scribe mirror binds the full Lean-derived statements and resolves this
problem slug.

The direct frozen dependency is
`D5.S1.Recurrence.Witt.PrimitiveEulerLedger.unique_primitive_euler_ledger`,
declaration statement identity
`sha256:d165385fc17ed8b6f40903b9a54d714049fa6c69196e3426b06a84e1c43430a7`
and type SHA-256
`sha256:7fe8f99b466b2459850676d666d61d2d11a69576aa657530b82082577d75527e`.
Its frozen module source SHA-256 is
`2628f7180dcc33c2ef4bcf6870e90896ce2f6ab9a42b406e045976a5c474cf29`;
the distinct module state pin is
`sha256:f0c96019644e8f7015f0a92bf5447b5e0cf6494450b7bfa25b2ed32cd2da1f39`.
The endpoint reuses that declaration directly rather than introducing a
wrapper or another uniqueness theorem.

## Triage

Both public theorems have `proof_shape: content` and
`admission_basis: escape-witness`. `loopy_spec` proves the concrete evaluator's
representation laws. The endpoint's live product and order inductions, new
specialization identity, exact finite Represents transport and recovery of all
counts form its escape content. No bind-only exception, open-problem exception,
helper theorem, numerical enumeration or certified positive instance is used.
The local product and order facts are not separate theorem nodes.

## ASSUMED-UNVERIFIED

The caller read the arXiv HTML at the four recorded locators; its SHA-256 is
`e38f48ed00c59fd2a80f59395a3b08c6a42ea0ead467ac5cce029b3886394332`.
The PDF SHA-256 is
`f3d4ae846384717ecce1c31261f021f172dad47443c7dd635d1d15b64ddd8f12`.
The caller read the title on PDF page 1, the ordinary/refined distinction on
PDF pages 33--34, and the exact question on PDF page 63. PDF text extraction
drops the refined-L typography, so the corresponding HTML MathML and alt text
supply that distinction. The bounded source-v1 and
exact-phrase arXiv search found no reusable proof of this endpoint. Other
supplementary queries were inconclusive and are not evidence of absence.
Worldwide priority remains `ASSUMED-UNVERIFIED`; the conclusion is scoped to
the recorded search and the kernel-checked repository result.

## Falsifier

A valid pair of encodings with equal ordinary Loopy polynomials and different
complete degree multisets would refute the endpoint. A route that drops degree
zero, counts a loop once, assumes equal order, replaces the ordinary invariant
by the refined one, or proves only a bounded truncation would not answer the
stated problem.
