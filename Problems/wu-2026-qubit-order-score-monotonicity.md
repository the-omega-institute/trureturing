---
slug: wu-2026-qubit-order-score-monotonicity
bibkey: wu2026measurementorder
doi: 10.48550/arXiv.2611.24604
url: https://arxiv.org/abs/2611.24604v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurement/OrderScores/QubitJensenShannonMonotonicity.result
---

# Monotonicity of Wu’s qubit Jensen–Shannon order score

## Problem

Shengjun Wu, *Measurement-order dependence bounds uncertainty,
contextuality, steering, and Bell nonlocality*, arXiv:2611.24604v1,
§II.C, printed p. 4, after Theorem 1:

> On a grid of 250 points Ψ is strictly increasing [Fig. 1(a)], but we have no proof of monotonicity.

The source sets $t=\sin(\theta)/2$, with $0\le\theta\le\pi/2$ after
outcome relabeling. For each $t$ the score $\Psi(t)$ is the maximum of
the four-outcome Jensen–Shannon divergence in bits over all positive
semidefinite complex $2\times2$ matrices of trace one. The input matrix is
common to both orders. Outcomes are indexed by measurement, so the
records have entries $\operatorname{Tr}(\rho P_a Q_b P_a)$ and
$\operatorname{Tr}(\rho Q_b P_a Q_b)$ at the same pair $(a,b)$.
The quantifiers are $0\le t_1<t_2\le1/2\Rightarrow\Psi(t_1)<\Psi(t_2)$.
Section VIII repeats the open question.
[§II.C](https://arxiv.org/html/2611.24604v1#S2.SS3.p3.1)
[Definition 1](https://arxiv.org/html/2611.24604v1#Thmdefinition1)
[§VIII](https://arxiv.org/html/2611.24604v1#S8.p2)
[Preregistration #33491](https://github.com/the-omega-institute/trureturing/issues/33491)

## Motivation

Strict increase makes the qubit block with largest total variation
decide the Jensen–Shannon score in Wu’s Theorem 1. The paper states
this implication immediately after the open question.
[Theorem 1](https://arxiv.org/html/2611.24604v1#Thmtheorem1)

## Gap

The published v1 gives the orthogonal endpoint and a one-point lower
bound. The author’s supplement reproduces the numerical curve.
Qualification for the tier-one target found zero indexed OpenAlex citations
and no exact proof in the inspected public topical results or in the
all-state repository issue and pull-request search before #33491.
The Semantic Scholar citation endpoint returned HTTP 429.
[OpenAlex record](https://openalex.org/W7236853850)
[Author’s supplement](https://github.com/Affinewu/measurement_order/tree/be936d4124d271eb3ef92e6e532b00f58ed233b7)
[Preregistration #33491](https://github.com/the-omega-institute/trureturing/issues/33491)

## Route

On the closed interval, set $s=(1-\sqrt{1-4t^2})/2$. The all-real Lean
definitions use the total root $\sqrt{\max(0,x)}$ for an argument $x$.
The two conventions agree wherever the radicand is nonnegative.
In the bisector frame the unit axes are
$(\sqrt{s},0,\sqrt{1-s})$ and $(-\sqrt{s},0,\sqrt{1-s})$.
In Wu’s normal form the observables are $\sigma_z$ and
$\cos\theta\,\sigma_z+\sin\theta\,\sigma_x$. To relate the frames, put
$m=\sqrt{1-s}$, $k=\sqrt{s}$,
$c=\sqrt{(1+m)/2}$, and $d=\sqrt{(1-m)/2}$.
Conjugate both bisector observables by
$\sigma_z\begin{pmatrix}c&d\\-d&c\end{pmatrix}$.
The identities $c^2+d^2=1$, $c^2-d^2=m$, and $2cd=k$ give
$\sigma_z$ and $(m^2-k^2)\sigma_z+2mk\sigma_x$ by matrix
multiplication. The same formulas hold at the two endpoints.
The angle satisfies $\theta=\arccos(1-2s)\in[0,\pi/2]$ and
$\sin(\theta)/2=t$. The acute coefficients are $\cos\theta$ and
$\sin\theta$. Common conjugation bijectively transports the available
native states. Reversing the second axis relabels its outcomes in both
records, which preserves the same range for the antipodal second axis.
Conjugating both observables by $\sigma_z$ then gives the
supplementary-angle convention with nonnegative X component.

Both joint laws have the same parity masses $1-s$ and $s$.
Writing $u=\sqrt{1-s}\,z$ and $v=\sqrt{s}\,x$, the biases of the two
records and their mixture yield the score in nats
$[g(u+v)+g(u-v)]/2-(1-s)g(u)-sg(v)$, where
$g(y)=\ln 2-h_{\mathrm{nat}}((1+y)/2)$.
The parity entropy cancels even when $s=0$. Every point of the closed
disk $x^2+z^2\le1$ is realized by a native state and the score attains its
maximum.

The entropy deficit has a convergent even series at both extreme biases.
A common circle point of the form $(\sqrt{w},\sqrt{1-w})$ dominates
the disk point coefficient by coefficient. Reflection and a one-sign-change
derivative argument allow $s\le w\le1/2$. To increase $s$, keep $u$
fixed up to $w=s$, then move along $w=s$. Each step weakly increases
all coefficients at the same circle point. The quadratic coefficient is
$s(1-s)=t^2$, and its weight is $1/2$ in nats.

## Falsifier

A pair $0\le t_1<t_2\le1/2$ with
$\Psi(t_2)\le\Psi(t_1)$ for the native common-state score would refute
the delivered statement. A mismatch in the labelled Lüders records,
bits conversion, angle calibration, or native maximum would invalidate
the identification with the source.

## Evidence

`QubitJensenShannon.sourceScore` and `psi` encode the native objective
and supremum. `native_maximum` attains the supremum using the exact
native-to-disk score correspondence. Separate Lean verification checks
both normalized labelled records, acute angle calibration, and equality
of the entire score range in Wu’s frame, including the antipodal branch.
It also checks $s(1)=1/2$ and
$\operatorname{circlePoint}(-1)=(0,\sqrt{2})$ for the total-root convention.
The decision theorem is
`D5/S3/Quantum/Measurement/OrderScores/QubitJensenShannonMonotonicity.result`.
The two scoped modules use only the standard Lean axioms. The §3.9
audit for their eight public theorems remains incomplete. The exact
source-selected realizations, intervention, sensitivity, actual observational
dependence, and producer binding evidence are tracked in the registration
issue. [#33502](https://github.com/the-omega-institute/trureturing/issues/33502)

## Triage

### What the settlement shows

- **Kernel-checked.** The proof of `quantitative_increase` starts with a
  maximizing circle representative at the first angle. The transport
  lemma `restricted_transport` finds one circle point at the second angle
  that weakly increases every even coefficient. The quadratic term
  supplies the gain $\Psi(t_2)-\Psi(t_1)\ge (t_2^2-t_1^2)/(2\ln2)$.
  The theorem `result` uses its positivity to prove strict increase.
- **Kernel-checked separately.** At coincident axes $\Psi(0)=0$.
  At orthogonal axes $\Psi(1/2)=h_2(3/4)-1/2$, the value already
  established by Wu’s Theorem 1 and Appendix A. The allowed maximizing
  circle interval collapses to $w=1/2$ at the orthogonal endpoint.
  [Appendix A](https://arxiv.org/html/2611.24604v1#A1.p2.1)
- **Proved in prose using the published block reduction.** Wu’s Theorem 1
  writes the optimized score of a binary sharp pair as
  $\max_j\Psi(t_j)$ and its total-variation score as $\max_j t_j$.
  Strict increase gives $J(A,B)=\Psi(T(A,B))$ and preserves the
  ranking, including ties. The delivered Lean theorem concerns the
  qubit function. The finite-dimensional block reduction used in this
  inference is supplied by the paper.
  [Theorem 1 and §II.C](https://arxiv.org/html/2611.24604v1#S2.SS3)
- **Unresolved here.** Optimality of the quantitative gain constant,
  classification of all maximizing states, and the behavior of the order
  scores under coarse-graining from §VIII remain open here.

## ASSUMED-UNVERIFIED

Priority outside the inspected public literature and indexes is unverified.
The §3.9 registry issue records missing realizations and binding evidence.
