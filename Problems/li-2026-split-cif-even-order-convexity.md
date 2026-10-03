---
slug: li-2026-split-cif-even-order-convexity
bibkey: li2026splitcif
doi: null
url: https://arxiv.org/abs/2606.27260v1
triage: theorem
motivation_gids:
  - D5/S3/Estimation/SplitCovarianceIntersectionEvenConvexity.result
---

# Arbitrary even-order convexity of split covariance intersection

## Problem

Hao Li, “Conjecture About Arbitrary Even-Order Convexity of w-Optimization
of the Split CIF”, arXiv:2606.27260v1, Section 2.2, equations (7a) and (7b),
states:

> The proposed conjecture is that **the w-optimization problem has arbitrary
> even-order convexity**, more specifically, for $k \in \{1,2,3,\cdots\}$ we always have

$$\frac{d^{2k}}{dw^{2k}}\ln\det(P(w))\geq 0,
\qquad \frac{d^{2k}}{dw^{2k}}\operatorname{tr}(P(w))\geq 0.$$

Issue [#11592](https://github.com/the-omega-institute/trureturing/issues/11592)
preregisters the source quotations, quantified statement, Tier 1 classification
and literature-search boundary. The reading retains both inequalities for
every positive even order and every interior weight, with the semidefinite
hypotheses of Section 2.1.

## Motivation

For real symmetric matrices A, B, C, D of any finite dimension, assume each
is positive semidefinite and A+B and C+D are positive definite. Equation (1)
defines P1(w)=A/w+B, P2(w)=C/(1−w)+D and
P(w)=(P1(w)⁻¹+P2(w)⁻¹)⁻¹. Scalar division in Lean is reciprocal scalar
multiplication. Mathlib PosSemidef includes symmetry over the reals.
The source assigns endpoint values by limits; the formal conjecture concerns
only 0<w<1 and makes no endpoint derivative assertion.

## Gap

The literature check in #11592 records only arXiv v1 and no later settlement
in its arXiv title, author and split-covariance-intersection search scope.
Its citation-index, MathDB and formal-conjectures checks are
ASSUMED-UNVERIFIED. This bounded search result establishes neither an
exhaustive literature search nor a priority claim. The fourth-order log-det
case cited there does not supply both objectives at every positive even order.

## Route

For positive definite inputs, form the affine three-block pencil

M(w)=[[wA⁻¹+(1−w)C⁻¹, −wA⁻¹, −(1−w)C⁻¹],
      [−wA⁻¹, wA⁻¹+B⁻¹, 0],
      [−(1−w)C⁻¹, 0, (1−w)C⁻¹+D⁻¹]].

Its quadratic form is the sum of the two weighted difference energies and
the B⁻¹ and D⁻¹ energies. Schur complementation identifies P with the upper
corner of M⁻¹ and gives det(P)=det(K)/det(M), where K is the lower two-block
compression. Even inverse derivatives are positive semidefinite after a
congruence. Diagonalization and Jensen for squared eigenvector overlaps give
the even-power trace comparison for an isometric compression. It yields the
log-det derivative inequality. Replacing each input by its sum with εI and
letting ε decrease to zero retains both inequalities; joint smoothness makes
each fixed-order derivative continuous in ε at every interior weight.

## Falsifier

Both objectives, arbitrary dimension and derivative order, all four
semidefinite assumptions and both positive definite pair-sum assumptions are
part of the quantified claim. Neither commutativity nor individual positive
definiteness is an additional hypothesis. A result restricted to fixed orders,
commuting inputs or individually definite inputs would not settle this
reading. Endpoint derivatives and the source's endpoint limit convention
are outside the statement.

## Evidence

The source is
`D5/S3/Estimation/SplitCovarianceIntersectionEvenConvexity.lean`.
Its public definitions are `splitP` and `claim`; its sole public theorem is
`result : claim`. Auxiliary derivative and compression arguments occur inside
that proof. The result's proof shape is content and its admission basis is
open-problem-resolution (#11592; Proved). Its escape witness is the public
conclusion itself, produced by the arbitrary-order affine-inverse and
log-determinant differential constructions together with the compression
trace inequality (the second permitted form of CLAUDE.md §3.2). Pinned
Mathlib supplies first-derivative calculus, spectral and convexity
prerequisites, but neither arbitrary-order differential formula; the module
imports no D5 theorem. The canonical
Scribe mirror records the Proved resolution of this dossier.

## Triage

Tier 1: a published 2026 conjecture, with the searched-scope literature
boundary recorded in #11592. The theorem settles its preregistered interior
reading, including semidefinite inputs.

### What the settlement shows

- **Proved in this module:** both inequalities hold for every k≥1, every
  finite real dimension and every interior weight. Positive definiteness of
  the individual inputs and commutativity are unnecessary.
- **Proved within the result's derivation:** the affine block representation
  links the trace objective to an inverse corner and the log-det objective to
  a determinant ratio. Isometric compression and scalar even-power convexity
  supply the sign comparison; regularization transfers it to semidefinite
  inputs. These are proof-internal mechanisms, not additional public theorems.
- **Proved in this module:** k=1 and k=2 are included together with every
  larger order. Any use of the source conjecture requiring exactly these
  interior inequalities can use `result`; other statements in the source
  papers are outside this formalization.
- **Open:** endpoint differentiability under the limit convention, equality
  cases and conditions for strict positivity, and weaker pair-sum assumptions.
  No assertion about these extensions is part of `result`.

## ASSUMED-UNVERIFIED

The citation-index, MathDB and formal-conjectures search reports in #11592
retain that status. The literature conclusion is only
not-found-in-searched-scope. No literature-wide novelty or priority claim
is made. Escape-audit registration is unfinished under the linked-issue
exception; its actual obstruction and missing evidence are recorded in
https://github.com/the-omega-institute/trureturing/issues/11592#issuecomment-5931604845
and refer to #11269.
