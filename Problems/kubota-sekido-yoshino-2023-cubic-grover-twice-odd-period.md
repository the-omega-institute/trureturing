---
slug: kubota-sekido-yoshino-2023-cubic-grover-twice-odd-period
bibkey: kubota2025evenperiodic
doi: 10.1016/j.disc.2024.114345
url: https://arxiv.org/abs/2307.13227v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Dynamics/CubicGroverTwiceOddPeriod.result
---

# Cubic Grover walks cannot have twice an odd period

## Problem

S. Kubota, H. Sekido and K. Yoshino, *Regular graphs to induce even
periodic Grover walks*, arXiv:2307.13227v1, Discrete Mathematics 348
(2025) 114345, ask after Theorem 4.10:

> Question 4.11. Let l be an odd integer that is a multiple of 3. Do 2l-periodic 3-regular graphs exist?

Graphs have the scope of §2.1: finite, simple, connected and undirected.
An arc is an ordered adjacent pair, represented by Mathlib's `G.Dart`;
its origin, terminus and reversal are `a.fst`, `a.snd` and `a.symm`.
Section 2.2 defines the complex Grover matrix by

$$
U_{a,b}=\begin{cases}
2/\deg_G(t(b))-1 & a=b^{-1},\\
2/\deg_G(t(b)) & t(b)=o(a),\ a\ne b^{-1},\\
0 & t(b)\ne o(a).
\end{cases}
$$

The period is the least positive integer $\tau$ with $U^\tau=I$.
The precise claim in issue #12338 uses $l\in\mathbb N$, `Odd l`,
`3 ∣ l`, a finite vertex type, connectedness, degree three at every
vertex, and the negation of period $2l$. Oddness already excludes zero;
the natural-number formulation preserves the source's positive periods.

## Motivation

The frozen declaration
`D5/S3/Quantum/Dynamics/CubicGroverTwiceOddPeriod.result` answers this
question negatively. The obstruction acts on the exact arc evolution
matrix; it requires neither a spectral classification nor a restricted
family of graphs.

## Gap

Issue #12338 preregisters a Tier 1 published question and the bounded
literature check. Its orchestrator-reported check covers the source,
the citing works arXiv:2609.08315, 2607.14797, 2605.02254, 2508.09711,
2506.07439 and 2502.10217, the integral-regular classification in
arXiv:2405.01020, and MathDB queries. The reported conclusion is
`not-found-in-searched-scope` for a general answer. The six-periodic
classification addresses $l=3$ separately. These readings do not
establish worldwide priority or exclude an independent solution.

## Route

For a cubic graph let $W=3U$, an integer matrix, and $X=W^2$.
Modulo two, $W$ is the arc-reversal permutation matrix, so $X\equiv I$.
For each arc $a$, the unique arc contributing to the diagonal of $W^2$
is $a^{-1}$, and $X_{a,a}=1$.

Assume $U^{2l}=I$ with $l$ odd. Then $X^l=(9I)^l$. Define

$$
Q=\sum_{i=0}^{l-1}X^i(9I)^{l-1-i}.
$$

The difference-of-powers identity gives $(X-9I)Q=0$.
Reduction modulo two gives $Q\equiv lI\equiv I$; hence its determinant
reduces to one and is nonzero over the integers. Multiplying by the
adjugate and cancelling the nonzero determinant gives $X=9I$.
Connectedness provides a vertex, and degree three provides an incident
arc. Its diagonal then gives $1=9$, a contradiction.

## Falsifier

A finite simple connected cubic graph with the displayed Grover matrix
and a positive odd $l$ satisfying $U^{2l}=I$ would falsify the stronger
local conclusion proved inside `result`. The theorem excludes every
such realization. A different evolution operator or an even $l$
changes the target.

## Evidence

The mathematical source is
`D5/S3/Quantum/Dynamics/CubicGroverTwiceOddPeriod.lean`.
Its public declarations are exactly `grover`, `IsPeriodOf`, `claim`
and the settling theorem `result : claim`. Its only private definition
is the integer numerator; all intermediate propositions are local
`have`s. It directly uses Mathlib's darts, endpoints, reversal and
matrix row reindexing.

The live local fact `heq` establishes the conditional rigidity
`numerator G ^ 2 = 9` under cubic regularity, `Odd l` and
`grover G ^ (2 * l) = 1`. Its proof uses the modulo-two reduction of
the difference-of-powers factor and determinant cancellation, and its
diagonal evaluation is used in the final contradiction. The axiom
closure of `result` is exactly `propext`, `Classical.choice` and
`Quot.sound`.

## Triage

Tier 1 published question; resolution `Proved` by
`D5/S3/Quantum/Dynamics/CubicGroverTwiceOddPeriod.result`.
`proof_shape: content`; `admission_basis: open-problem-resolution`
(issue #12338, witness v2). Utility `none`: this is a general theorem,
with no retained finite graph certificate, bounded enumeration,
numerical reduction or checker implementation.

### What the settlement shows

- **Proved in this module:** the local fact `stronger` proves
  $U^{2l}\ne I$ for every odd $l$, without assuming $3\mid l$.
  The public result preserves the exact preregistered statement.
- **Proved in this module:** the decisive mechanism is the conditional
  rigidity $W^2=9I$ and the incompatible diagonal $1$. Connectedness
  supplies a vertex; cubic degree supplies an arc. No eigenvalue or
  integrality hypothesis is imposed on the graph.
- **Open (Lean formalization); written observation:** for every odd
  regular degree $k\ge3$ the same construction uses $W=kU$,
  $W\equiv S\pmod2$ and $(W^2)_{a,a}=(2-k)^2$. The odd determinant
  argument would force $W^2=k^2I$, whereas
  $(2-k)^2-k^2=4(1-k)\ne0$. This extension is not a declaration or a
  proved result of this module.
- **Open (Lean formalization); written consequence using the source:**
  Theorem 4.10 allows a regular graph of period $2l$ only to be
  $C_{2l}$ or to be cubic with $3\mid l$. The settling result excludes
  the cubic alternative. Together with the source's cycle-period
  result this leaves only $C_{2l}$ for odd $l\ge3$. Theorem 4.10 and
  that classification are literature inputs, not formalized here.
- **Open (independent literature verification in this delivery):**
  issue #12338 reports that Kubota's six-periodic classification,
  arXiv:2609.08315, excludes cubic graphs and therefore answers $l=3$.
  This is an orchestrator-reported special case, not a second result
  proved by this module.
- **Open:** the source's questions for periods divisible by four are
  outside the odd-$l$ obstruction. The proof supplies no classification
  in that regime; the source's period-four $K_{3,3}$ is compatible with
  this answer. The source's already proved necessary conditions remain
  usable; its unresolved cubic alternative is excluded.

## ASSUMED-UNVERIFIED

Worldwide priority and exhaustive literature coverage are not verified.
The literature search in #12338 is attributed to the orchestrator;
the published definitions and Question 4.11 are the source for the
statement echo. The Lean kernel verifies the encoded theorem, not
the exhaustiveness of that literature search. The odd-degree extension
and the combined regular-graph classification are written consequences
outside this module's formal declarations.
