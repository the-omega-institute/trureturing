---
slug: nuradha-2025-z-fidelity-distance
bibkey: nuradha2025multivariate
doi: 10.1088/1751-8121/adc645
url: https://arxiv.org/abs/2404.16101v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/ZFidelityDistanceRefutation.result
---

# Whether the z-fidelity distance is a distance measure

## Problem

T. Nuradha, H. K. Mishra, F. Leditzky and M. M. Wilde, *Multivariate
Fidelities*, J. Phys. A 58, 165304 (2025), arXiv:2404.16101v3, Section 6,
open question 3:

> Is $\sqrt{2(1-F_z(\rho,\sigma))}$ a distance measure for
> $z \in (1/2,1)\cup(1,\infty)$?

The $z$-fidelity is
$F_z(\rho,\sigma)=\mathrm{Tr}[(\sigma^{1/(4z)}\rho^{1/(2z)}\sigma^{1/(4z)})^z]$
(Eq. (eq:z-fid-def)).

## Motivation

The paper notes that a positive answer would give uniform continuity bounds
for average pairwise $z$-fidelities, as its Bures-distance argument does at
$z=1/2$. The frozen declaration
`D5/S3/Quantum/Information/ZFidelityDistanceRefutation.result` shows that the
answer is negative on the stated range.

## Gap

Issue #12705 classifies the question as Tier 1 and records the checks made
before any Lean:

- arXiv:2404.16101 v3 (June 2025) is the latest version.
- The 11 forward citations listed by Semantic Scholar on 2026-10-04 were
  screened. Five were searched in source for statements on the metric
  property of $\sqrt{2(1-F_z)}$, with no hit: arXiv:2410.04937, 2605.28885,
  2609.34699, 2601.17850 and 2505.16715.
- arXiv:2605.28885 uses $F_z$ but does not address the triangle inequality.

These are orchestrator-checked readings, `not-found-in-searched-scope`; they
do not establish exhaustive worldwide novelty.

## Route

1. $z=2$, with $P=\frac1{10}\begin{pmatrix}9&3\\3&1\end{pmatrix}$,
   $Q=\frac1{17}\mathrm{diag}(16,1)$ and
   $T=\frac1{10}\begin{pmatrix}9&-3\\-3&1\end{pmatrix}$.
2. $P$ and $T$ are positive idempotents, so $P^r=P$ and $T^r=T$ for $r>0$:
   the spectrum of an idempotent lies in $\{0,1\}$, where $x^r=x$.
3. Uniqueness of positive square roots gives
   $\sqrt Q=\mathrm{diag}(4,1)/\sqrt{17}$ and
   $Q^{1/4}=\mathrm{diag}(2,1)/17^{1/4}$; also
   $Q^{1/8}Q^{1/8}=Q^{1/4}$.
4. Hence $F_2(P,T)=\frac{256}{625}$ and
   $F_2(P,Q)=F_2(Q,T)=\frac{361}{100\sqrt{17}}$.
5. The triangle inequality $d(P,T)\le d(P,Q)+d(Q,T)$ would force
   $\frac{361}{100\sqrt{17}}\le\frac{2131}{2500}$. This fails, because
   $9025^2-17\cdot2131^2=4250888>0$.

## Falsifier

The kernel-checked `result` is the negation of the following statement. For
every real $z$ with $1/2<z<1$ or $z>1$, every $n$, and all $n\times n$
complex positive semidefinite matrices $\rho,\sigma,\tau$ of trace one,
$\sqrt{2(1-F_z(\rho,\tau))}\le\sqrt{2(1-F_z(\rho,\sigma))}+
\sqrt{2(1-F_z(\sigma,\tau))}$.

The definitions are as follows:

- $F_z$ is Eq. (eq:z-fid-def), with real powers of positive semidefinite
  matrices taken in Mathlib's continuous functional calculus (`CFC.rpow`)
  and the real part of the trace recorded. The trace is real for positive
  arguments.
- The triangle inequality is part of being a distance measure, so its
  failure answers the question negatively.

## Evidence

Numerical recomputation (issue #12705, orchestrator): scipy fractional matrix
powers on the literal definition give $d(P,T)\approx1.0866$ and
$d(P,Q)+d(Q,T)\approx0.9978$ at $z=2$.

The canonical source is
`D5/S3/Quantum/Information/ZFidelityDistanceRefutation.lean`. Its public
declarations are `zFidelity`, `zDistance`, `claim`, `stateP`, `stateQ`,
`stateT` and `result`.
FREEZE_IDENTITIES
The proof uses only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`; no `sorry`, `native_decide`, or new axiom.

## Triage

Tier 1 open question of a 2025 journal article; resolution `Refuted` by
`D5/S3/Quantum/Information/ZFidelityDistanceRefutation.result`.
`proof_shape: bind-only` (the settlement of the named question is the new
content; no escape witness); `admission_basis: open-problem-resolution`
(issue #12705). Utility kind `certified-instance`, basis `refutes` the
module's `claim`.

### What the settlement shows

- **Proved by `result`:** the distance $\sqrt{2(1-F_z)}$ is not a distance
  measure on the whole range $(1/2,1)\cup(1,\infty)$: at $z=2$ the triangle
  inequality fails on qubits.
- **Proved inside the proof of `result`:**
  - every positive real power of a positive idempotent $2\times2$ matrix is
    the matrix itself;
  - the square roots of $Q$ are as stated;
  - $F_2(P,T)=256/625$ and $F_2(P,Q)=F_2(Q,T)=361/(100\sqrt{17})$.
- **Mechanism (orchestrator argument and numerics, not stated in Lean):**
  - For rank-one projections $|\psi\rangle\langle\psi|$ and
    $|\phi\rangle\langle\phi|$ the paper's own formula gives
    $F_z=|\langle\psi|\phi\rangle|^{2z}$ (l. 123), so the distance between
    $P$ and $T$ grows with $z$, while the diagonal state $Q$ stays close to
    both.
  - For these three states, the gap $d(P,T)-d(P,Q)-d(Q,T)$ was computed with
    scipy fractional matrix powers. It is negative at
    $z=0.55,0.7,0.9,1.1,1.2,1.3$ and positive at $z=1.4,1.5,2,3,5,10$
    ($0.0084$ at $1.4$, $0.0888$ at $2$, $0.3027$ at $10$). The triangle
    inequality therefore fails for this triple from about $z\approx1.35$
    onward, and not on $(1/2,1)$.

- **Effect on the paper's other conclusions:** the paper's uniform
  continuity bounds use the Bures distance ($z=1/2$, l. 600–604), which the
  paper recalls is a metric. These bounds are unaffected; the hoped-for
  extension to general $z$ through this distance is not available on the
  whole range.
- **Open here:**
  - the exact set of $z$ in $(1/2,1)\cup(1,\infty)$ for which the triangle
    inequality holds;
  - whether it fails for every $z>1$, and whether it holds on $(1/2,1)$.
  These are not settled by this counterexample.

## ASSUMED-UNVERIFIED

The literature checks do not establish worldwide priority, and a complete
forward-citation graph was not obtained. The Lean kernel verifies the encoded
statement and its axiom closure. Its correspondence to the paper is checked by
reading the source and the definitions, including the reading of "distance
measure" through the triangle inequality and of matrix powers through the
continuous functional calculus.
