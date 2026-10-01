---
slug: lundqvist-schulze-stokes-symmetric-scenes-lifting-refutation
bibkey: lundqvist2026symmetricscenes
doi: 10.48550/arXiv.2609.27605
url: https://arxiv.org/html/2609.27605v1#S6
triage: theorem
motivation_gids:
  - D5/S3/Geometry/SymmetricScenesRefutation.result
---

# Symmetric scenes: lifting sufficiency

## Problem

Conjecture 6.1 states: “The necessary conditions of Corollary 3.10 and
Corollary 4.8 are sufficient for Γ-generic pictures and hyperplane
arrangements.” The lifting assertion quantifies over every finite connected
labelled incidence geometry, finite free faithful group action, orthogonal
representation and sign character, actual orbit-representative gain chart,
and every generic symmetric picture. The exact equality and every
incidence-orbit subset inequality must imply minimal symmetric flatness.
`OriginalSource.liftingSufficiency` states this complete lifting telescope.

## Motivation

Subset counts control available equations. They need not prevent geometric
row dependencies forced by the symmetry of a genuine incidence hypergraph.
The ordinary graph case is already known and is outside this target.

## Gap

The source prints Conjecture 6.1. Issue #11601 preregisters its complete
lifting clause and the bounded C2 counterexample. The primary HTML and
arXiv abstract page, retrieved 2026-10-01, retain Conjecture 6.1 and list
only v1. The five-result Crossref exact-title wording query found no
settlement in its returned titles; OpenAlex returned HTTP 429, so its
current indexed status was not verified. The earlier issue's literature
checks remain limited to their stated scope. No exhaustive absence or
publication-priority claim follows from these checks.

## Route

Use d=3, Γ=C2, the half-turn τ=-I2, and the trivial character. There are
three point-orbit labels and two hyperplane-orbit labels. Each hyperplane
has gain incidences (P0,0), (P0,1), (P1,0), (P2,0). The full cover has
six point labels, four hyperplane labels and sixteen distinct incidences.
It is connected, its label action is free and faithful, and each
hyperplane has four incident points.

The proof constructs an actual GainChart and transports every original
incidence-orbit subset to its exact eight-edge mask. Supported vertex
reachability, component quotients and all unbounded closed-gain walks
are preserved. Component weights use genuine invariant submodules;
linear equivalence preserves their finranks. Algebraic independence is
transported to the actual representative-coordinate family.

For representative coordinates (a,b), (c,d), (e,f), take positive-copy
normals (-b,a), zero constants, and heights 0, −(ad−bc), −(af−be).
The half-turn negates normals and preserves heights. The literal scene
satisfies every incidence equation, but opposite-copy normals differ
because algebraic independence implies a≠0. It is therefore nonflat.

## Falsifier

A missing standing source clause, a gain chart that fails to realize its
actual incidence orbits, an omitted subset or component, a dimension
proxy replacing H, loss of representative genericity, or a trivial scene
would invalidate the refutation. The Lean proof closes each of these
mathematical obligations on the same labelled geometry and scene.

## Evidence

`D5/S3/Geometry/SymmetricScenesRefutation.result` has type
`Not OriginalSource.liftingSufficiency`. The scoped canonical D5 and Reg
build succeeds in Lean 4.33.0 with Mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d` on base
`d6548d50ec4da15b91d7911dc060ef45e407b88f`. The exact-negation
application is kernel checked. Its axiom closure is `propext`,
`Classical.choice`, and `Quot.sound`.

The source-owned Reg mirror compiles. The existing external
`finiteInformationTemplateReportDriver` returns one `declared_validated`
four-slot record with a witness bridge from the literal `Nat` binder and
an `open` residual. Its statement identity is
`8552ff8799a4b0569bf8ffb7f1c66a0d7c901560a4d31be8ae50570034651fcf`;
its evidence reference is
`db33d47f035e2dd57f3fd70e5cd59c87eff27e97f022a369bf9a39b6848b1859`.

The fixed-C2 witness is `witnessData`; the single public theorem is the
original-source negation, with `admission_basis: open-problem-resolution`.
The full mathematical telescope and witness retain the same labelled
geometry, actual gain chart, every subset and component, genuine
invariant-submodule dimensions, unbounded closed-gain walks,
algebraically independent representative coordinates and nonflat scene.

## Triage

### What the refutation shows

Kernel conclusion (`D5/S3/Geometry/SymmetricScenesRefutation.result`):
the complete lifting-sufficiency predicate is false. The counterexample mechanism is a symmetry-forced dependence retained
by the two distinct hyperplane labels with identical neighborhoods.
Nonflatness defeats both incidence-deletion and orbit-deletion notions
of minimal flatness, since each includes flatness. Only the literal
incidence-deletion conclusion is formally stated as the resolution theorem.
Open: the parallel-redrawing clause, Conjecture 6.2 and variants with
neighborhood injectivity, sharpness or a weaker sparsity condition.
The necessary-count corollaries are not contradicted: the failure is
in the conjectured converse. The source's established ordinary-graph
case is outside this incidence-hypergraph counterexample. No new
corrected-conjecture theorem follows from the refutation.

## ASSUMED-UNVERIFIED

OpenAlex's current indexed status was not
verified because its bounded query returned HTTP 429. The bounded
source and literature checks do not exclude unindexed, unpublished or
differently titled prior settlements.
