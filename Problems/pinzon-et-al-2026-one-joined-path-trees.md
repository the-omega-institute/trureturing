---
slug: pinzon-et-al-2026-one-joined-path-trees
bibkey: pinzonetal2026onejoinedpaths
doi: null
url: https://arxiv.org/pdf/2611.34794v1#page=9
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/LinearForests/OneJoinedPathTrees.oneJoined_iff_spineCut
---

# Pinzon et al. on trees formed by one-joining paths

## Problem

“Which trees can be formed by one-joining paths? Can we classify those trees?”
The input is any finite nonempty simple tree, with classification up to graph
isomorphism. A one-join attaches the largest label of a path block to label 1
of the next path block. The bijective labelling of each path is arbitrary.
The two choices of minimum block order, one and two, are independent of
whether the chain must have an actual join. [Pinzon et al., §§1, 3, 6](https://arxiv.org/pdf/2611.34794v1#page=9)

## Motivation

Tier 1. The 2026 preprint explicitly asks for a classification in its final
section. Issue #34504 registers both directions and four conventions, with
forecasts recorded before the finite probe and before the unbounded proof.
[Preregistration and discussion](https://github.com/the-omega-institute/trureturing/issues/34504) · [Forecasts](https://github.com/the-omega-institute/trureturing/issues/34504#issuecomment-7193929991)

## Gap

The cited earlier j-join work introduces the attachment rule and studies
determinant representations. The preregistration records searches yielding
no exact classification. It also records the scope differences for a
grid-based path-like tree definition and for path covers. [Preregistration](https://github.com/the-omega-institute/trureturing/issues/34504) · [Definition 1.1](https://arxiv.org/pdf/2409.02355v2#page=2) · [Path-like trees](https://arxiv.org/abs/1705.08802v2) · [Path-cover paper](https://arxiv.org/abs/2511.07160v1)

## Route

Choose a simple path and a set C of its edges. Write d for original degree
and c for incidence in C. For minimum block order two, require c ≤ 1
and 1 ≤ d − c ≤ 2 at every vertex. For minimum order one, require
0 ≤ d − c ≤ 2 and c = 2 only at vertices with d = 2. A cut on a
simple path has at most two incidences per vertex. The actual-join
conventions require a nonempty C. Each closure permits an empty C.

The forward proof takes the actual joins. Consecutive block boundaries and
unique tree paths put them on one simple path. Deleting the joins leaves
exactly the intrablock adjacencies. The reverse proof projects the spine to
the quotient of the components after deleting C. Those components occur in
path order and have residual degree at most two, so each is a path. The
incoming and outgoing cut endpoints give label 1 and the maximum label,
respectively. The local degree conditions force any coincident ports onto
a singleton.

## Falsifier

A finite nonempty tree and one of the four conventions where only one side
holds would falsify the classification. For the stronger reconstruction,
a qualifying C that cannot be recovered as the exact interblock edge set
would falsify the certificate. The preregistered bounded probe made 5,768
comparisons on 1,442 labelled trees and exited zero. [Probe report](https://github.com/the-omega-institute/trureturing/issues/34504#issuecomment-7194203238)

## Evidence

The Proved claim links to `OneJoinedPathTrees.oneJoined_iff_spineCut`.
The exact witness theorem `OneJoinedPathTrees.realizes_spine_cut` recovers
each qualifying cut, with positive join count exactly when C is nonempty.
The forward certificate uses the presentation's own joins. The proof was
independently replayed under Lean 4.35.0 with official Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679` at trust level zero. The public
escape audit remains unfinished and is linked to the preregistration issue.
[Proof and audit issue](https://github.com/the-omega-institute/trureturing/issues/34504) · [Independent replay summary](https://github.com/the-omega-institute/trureturing/issues/34504#issuecomment-7194790841)

## Triage

The typed resolution records the classification under all four conventions.

### What the settlement shows

- Proved. The exact identity d = residual degree + c makes the incidence
  test a test in the original graph. A one-path cut controls the order of
  the residual blocks and reconstructs the same join edges.
- Proved. Within both minimum-order conventions, the zero-join case is a
  single path satisfying that minimum order. The classification supplies
  a finite recognition test by enumerating simple paths and their edge subsets.
- The determinant and monoid results in the source precede and do not rely on
  the classification. The source's questions about higher joins remain open
  in this dossier.

## ASSUMED-UNVERIFIED

The literature check covers the cited versions and the search reported in
the preregistration. Journal publication, complete forward-citation
coverage and worldwide priority are unverified. [Literature search record](https://github.com/the-omega-institute/trureturing/issues/34504)
