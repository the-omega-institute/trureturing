---
slug: bluhm-2025-appendix-a1-feasibility
bibkey: bluhm2025inclusion
doi: 10.48550/arXiv.2512.17706
url: https://arxiv.org/abs/2512.17706v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurement/FreeSpectrahedronFeasibilityWitness.result
---

# A single-formula feasibility witness for the qubit simplex-and-interval inclusion

## Problem

A. Bluhm, E. Evert, I. Klep, V. Magron and I. Nechita, *Inclusion constants for free spectrahedra
with applications to quantum incompatibility*, arXiv:2512.17706v1, Appendix A.1, conjecture that
the explicit tuple with
$C_1=(\tfrac1{\sqrt3}-\tfrac12)\begin{pmatrix}1&1\\1&1\end{pmatrix}$, the displayed $C_2(\theta)$ and
$C_3,\dots,C_6$ from Eq. (47) is feasible for the SDP (37) at $X(\theta)$, $\gamma=4/(1+\sqrt3)$, for
every $\theta\in[0,\pi/2]$. The verbatim statements are in
[the literature note](../Library/QuantumBounds/bluhm2025inclusion.md).

Issue [#14338](https://github.com/the-omega-institute/trureturing/issues/14338) reads "feasible" as
membership in $\mathfrak D_{\gamma,X(\theta)}$: all six matrices positive semidefinite in
$M_2(\mathbb C)$ and the four affine equations of (37).

## Motivation

The SDP (37) certifies that $X(\theta)$ lies in $\gamma\,\mathcal W^{\min}(\mathcal D_A(1))$
(the source's `prop:HKMFeasibilitySDP`), which gives the inclusion constant of the qubit simplex-and-interval free
spectrahedron used for joint measurability. Theorem 5.6 proves feasibility with a construction
split at $\pi/8$; the conjectured tuple is a single closed formula on the whole interval.

## Gap

The source reduces the conjecture to $\det C_2\ge0$ and states that it could not prove this.
Issue #14338 records the literature check before any Lean: only arXiv v1 exists; the citing paper
Evert–Graham arXiv:2608.24773 does not treat Appendix A.1; Zenodo has no record;
`not-found-in-searched-scope`.

## Route

With $r=\sqrt3$, $s=\sin\theta$, $c=\cos\theta$, $\beta^2=3((6-4r)s+6c-4r+13)$:
- the affine equations hold identically because Eq. (47) solves them;
- $C_1,C_4=(\tfrac1r-\tfrac12)\begin{pmatrix}1&\pm1\\ \pm1&1\end{pmatrix}$;
- $\beta^2=9(c+1)^2+(3s-2r+3)^2$, so $\det C_3=\det C_5=0$ and $\operatorname{tr}C_3=\operatorname{tr}C_5=\beta/6>0$;
- $144\det C_2=A-B\beta$ with $A=36c+228-96r>0$, $B=16r-12>0$, and
  $A^2-B^2\beta^2=144(1-s)(219+9s-124r)$, where $219-124\sqrt3>0$; hence $\det C_2\ge0$, and
  $\operatorname{tr}C_2=(8r-6-\beta)/6>0$; $C_6$ has the trace and determinant of $C_2$;
- a real symmetric $2\times2$ matrix with positive trace and nonnegative determinant is positive
  semidefinite as a complex matrix.

## Falsifier

The statement concerns the exact tuple of Appendix A.1 and the SDP (37) with $\gamma=4/(1+\sqrt3)$;
any other $C_1$, $C_2$ or $\gamma$ is outside the claim. The source's word "positive" for
$\det C_2$ is read as nonnegative: $\det C_2=0$ at $\theta=\pi/2$.

## Evidence

The canonical source is `D5/S3/Quantum/Measurement/FreeSpectrahedronFeasibilityWitness.lean`, with
public `claim` and `result : claim`. The axiom closure of `result` is exactly `propext`,
`Classical.choice` and `Quot.sound`; there is no `sorry`, `native_decide` or new axiom.
The module statement is `sha256:8e3161385dc8a9084195f1349f00b18a416e9ae9482194ae863e202c258865ac`,
the `result` statement `sha256:1079b821c67bfe8e831790fb1d2ca362e7b9bff08ff07a9f3c949bcb05e2ac90` and the
`claim` statement `sha256:888093d3ca035627875af0a6ca576c01c5f8fb2d4fab9dc2f6b2331646f6a2cf`. The Freeze
event is `sha256:115351b240dc71bb8eefa8f6aca18156a9f3b9c011aa80f0659d0db50da365b7`; its project-level
prerequisite is `D5/S3/Constants/Radicals/SqrtThreeThreshold` (frozen node
`sha256:eff322ff7062275040292c230faf45c194bb5d0cfc0f2d7a6aaa4cf65fc216c5`, module statement
`sha256:7772994aef5132c9610ed05ed595937b5ac5ac22b1cde9f80ba34f2c5f87a10b`), whose
`three_lt_two_mul_sqrt_three` gives $\sqrt3>3/2$.

## Triage

Tier 1 conjecture of a December 2025 paper, preregistered in issue #14338 before any Lean.
`theorem`; resolution `proved`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | content | `scalar_bounds`: $A-B\beta\ge0$ from $A^2-B^2\beta^2=144(1-s)(219+9s-124\sqrt3)$ | open-problem-resolution |

The private helpers `posSemidef_of_trace_det` (the $2\times2$ criterion), `scalar_bounds`,
`affine_eqs` and `matrix_forms` are each used on the proof of `result`.

Utility is `none`: the statement holds for every $\theta$ in an interval and is proved by symbolic
identities. There is no digestion atom.

### What the proof shows

**Proved by `result`:** the Appendix A.1 tuple is feasible for every $\theta\in[0,\pi/2]$, so a
single closed formula replaces the two-piece construction of Theorem 5.6.

**Argued or computed, not formalized.**

- *Mechanism.* $\beta$ is chosen so that $C_3$ and $C_5$ are rank one for every $\theta$
  ($\beta^2=9(c+1)^2+(3s-2r+3)^2$): the tuple stays on the boundary of the positive cone in those
  two blocks, and the only remaining constraint is the sign of $\det C_2=\det C_6$.
- *Where it is tight.* $\det C_2=0$ exactly when $\sin\theta=1$ (the factor $1-s$), so the tuple is
  on the boundary of the feasible set at $\theta=\pi/2$; elsewhere in $[0,\pi/2)$ $C_2$ and $C_6$
  are positive definite.
- *How far the formula extends.* Positivity of $C_1,C_3,C_4,C_5$, the
  identity of the Route and the positivity of $A$, $B$ and $\operatorname{tr}C_2$ hold for every
  real $\theta$: the radicand of $\beta$ has minimum $13-4\sqrt3-\sqrt{120-48\sqrt3}>0$ over
  $\theta$, because $(13-4\sqrt3)^2-(120-48\sqrt3)=97-56\sqrt3>0$ ($97^2=9409>9408=3\cdot56^2$);
  $A\ge192-96\sqrt3>0$; and $\beta^2\le3(13-4\sqrt3+\sqrt{120-48\sqrt3})<(8\sqrt3-6)^2$. Hence
  the tuple is feasible exactly when $\det C_2\ge0$, that is when
  $(1-\sin\theta)(219+9\sin\theta-124\sqrt3)\ge0$, i.e. $\sin\theta\ge(124\sqrt3-219)/9\approx-0.4695$.
  A floating-point classification of $72\,001$ angles in $[-\pi,\pi]$ (smallest eigenvalue of each
  $C_i$, tolerance $10^{-12}$) agrees with this arc.

**Open.** The source's conjectures on the optimal constant for larger simplices plus an interval
(`conj:kSimplexPlusLineOptimum`) and on four-line incompatibility ($s_\mathbb C(2,4)=2/\sqrt{13}$,
`conj:fourlines`) are not addressed; neither is whether witnesses of this rank-one-block shape exist
for them.

**Effect on the paper.** Theorem 5.6 now has a one-piece certificate; the inclusion constant
$\gamma=4/(1+\sqrt3)$ is unchanged.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty, priority, or
the absence of an independent proof.
