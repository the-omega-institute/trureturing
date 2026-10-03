---
slug: godsil-2011-average-mixing-discriminant-integrality
bibkey: godsil2013averagemixing
doi: 10.1016/j.jcta.2013.05.006
url: https://arxiv.org/abs/1103.2578v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Dynamics/AverageMixingDiscriminantIntegrality.result
---

# The discriminant clears average mixing denominators

## Problem

C. Godsil, *Average mixing of continuous quantum walks*, arXiv:1103.2578v3,
section 11, Question 1 (PDF page 20), asks:

> Is it true that if $D$ is the discriminant of the minimal polynomial of $X$, then $D\widehat M_X$ is an integer matrix?

For a finite simple graph $X$ with adjacency matrix $A$, the minimal
polynomial is taken over $\mathbb Q$. The source's Lemma 1.1 identifies
$\widehat M_X=\sum_\theta E_\theta\circ E_\theta$, with one orthogonal
spectral projector for each distinct eigenvalue. Lemma 3.1 establishes
only the factor $D^2$. Issue #12339 preregisters the exact all-graphs
assertion, with no connectedness or simple-spectrum restriction.

## Motivation

The frozen declaration
`D5/S3/Quantum/Dynamics/AverageMixingDiscriminantIntegrality.result`
answers Question 1 affirmatively. It reuses `idempotent` and `avgMixing`
from `AverageMixingTraceMaximum`; the transition-integral interpretation
is represented by the source's Lemma 1.1 spectral formula.

## Gap

Issue #12339 classifies the question as Tier 1 and records a bounded
literature check before any Lean probe. The arXiv v3 source retains
Question 1. The orchestrator reports full-text checks of arXiv:1709.07907,
1910.02039, 1709.03591, 2308.16378, 2211.02037, 2404.02236, 2208.08971
and 2608.20739, and MathDB searches for average mixing and discriminant:
no affirmative or negative settlement was found in that scope. These
are orchestrator-reported readings, `not-found-in-searched-scope`, and
do not establish worldwide priority or an exhaustive literature search.

## Route

The rational minimal polynomial of the symmetric integer adjacency
matrix is monic, squarefree and has integer coefficients. Its real roots
are exactly the distinct eigenvalues. For each root $\theta$, write
$f=(t-\theta)q_\theta$. Polynomial evaluation in the orthonormal eigenbasis
gives $q_\theta(A)=q_\theta(\theta)E_\theta$. Resultant multiplicativity
gives

$$\operatorname{disc}(f)=\operatorname{disc}(q_\theta)q_\theta(\theta)^2.$$

It follows, without dividing, that

$$D(E_\theta)_{ij}^2=\operatorname{disc}(q_\theta)(q_\theta(A)_{ij})^2.$$

The sum on the right over the roots is an integer polynomial in those
roots, invariant under permutations. The fundamental theorem of symmetric
polynomials expresses it in elementary symmetric functions. Vieta
identifies their values with signed integer coefficients of $f$. Thus
every entry of $D\widehat M_X$ is an integer.

## Falsifier

A finite simple graph and an entry of its source-defined average mixing
matrix for which the discriminant-scaled value is not an integer would
falsify Question 1. The kernel-checked `result : claim` excludes such an
entry for every natural vertex count. Mathlib gives discriminant 1 to
degree-one and constant polynomials; the zero-vertex case has no entries.

## Evidence

The canonical Lean module is
`D5/S3/Quantum/Dynamics/AverageMixingDiscriminantIntegrality.lean`.
Its public surface contains only `claim` and `result : claim`. All
auxiliary facts and constructions are local to `result`; there are no
private theorem wrappers or additional public results. The proof uses
`propext`, `Classical.choice` and `Quot.sound`, without `sorry`,
`native_decide` or a new axiom. The Scribe mirror records resolution
`Proved` for this question.

## Triage

Tier 1 published question; resolution `Proved` by
`D5/S3/Quantum/Dynamics/AverageMixingDiscriminantIntegrality.result`.
`proof_shape: content`; `admission_basis: open-problem-resolution`
(issue #12339). Utility `none`: the theorem covers every finite simple
graph rather than a bounded certificate.

### What the settlement shows

- **Proved in this module:** the decisive cancellation identity
  `discr_scaled_entry` and the permutation invariance
  `formalSum_symmetric` are local facts on the active proof path. They
  remove the squared spectral denominator and turn every scaled entry
  into the value of an integer symmetric polynomial.
- **Proved in this module:** the factor $D$ suffices for every finite
  simple graph, including disconnected graphs and repeated adjacency
  eigenvalues. For every graph, the denominator of the average mixing
  matrix divides $D$ in the integer-entry sense that $D\widehat M_X$
  has integer entries. The $D^2$ bound is unnecessary for Question 1.
  The delivered declaration is this integer-entry equation; no additional
  denominator theorem is exported.
- **Open generalization:** the same written argument for every real
  symmetric integer matrix. The delivered claim quantifies over simple
  graphs only; the broader matrix statement is not proved here.
- **Open:** a smaller natural divisor that clears the entries for every
  graph, and the sharpness of such a divisor. No optimality statement is
  included in the settlement.
- **Open here:** Questions 2 and 3 of section 11, concerning useful
  rational algorithms and average mixing matrices in the span of $I,J$.
  The answer to Question 1 strengthens Lemma 3.1's stated factor; no
  other theorem or algorithm in the source is claimed as a new
  consequence.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish worldwide novelty or
exclude an independent solution. Correspondence between the source's
transition-integral definition and the imported spectral expression
uses the published Lemma 1.1; this module does not formalize that
analytic limit. Independence of the spectral projectors from the chosen
orthonormal eigenbasis is a standard property documented by the frozen
owner, not an additional theorem in this module.
