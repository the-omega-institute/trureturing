---
slug: goodenough-landahl-2026-connected-progenitor-adaptive-fusion
bibkey: goodenough2026fusion
doi: null
url: https://arxiv.org/abs/2609.02559
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurements/ConnectedProgenitorPerfectAdaptiveFusion.result
---

# Connected progenitor graphs give perfect adaptive fusion strategies

## Problem

Goodenough, Landahl, Lee, Russo and Thompson, *Optimal Fusion Strategies for
Quantum Computation*, arXiv:2609.02559v2, study logical fusions of
$[[n,1,d]]$ codes: a failed physical fusion measures both qubits in its
failure axis, and failures on a set $W$ cause a logical failure iff the
substrings of the failure-axis string on $W$ contain a non-trivial logical
operator (Proposition 3.1). A strategy is perfect when one successful fusion
suffices. Section 6 reads

> So, a natural conjecture and direction of future work is that all
> $[[n, 1, d]]$ codes with connected progenitor graphs have perfect adaptive
> strategies.

Issue #13256 fixes the reading. Pauli strings are taken up to phase as
$(x,z)$ bits. The stabilizers of the progenitor graph state $G$ with encoding
vertex $e$ are the products $\Gamma_U$ of canonical generators. A non-trivial
logical operator is the restriction of some $\Gamma_U$ to $V\setminus\{e\}$
with $\Gamma_U$ not the identity at $e$. An adaptive strategy attempts the
physical vertices in a fixed order and chooses each failure axis (X, Y or Z)
from the earlier outcomes.

## Motivation

The paper characterizes perfect non-adaptive strategies and exhibits a
connected five-qubit code with none, while an adaptive strategy exists for it.
Perfect adaptive strategies reach the upper bound $1-(1-P_B)^n$ on the success
probability of a logical Bell measurement (Reiß and van Loock,
arXiv:2601.08820, Theorem 1).
`D5/S3/Quantum/Measurements/ConnectedProgenitorPerfectAdaptiveFusion.result`
proves the conjecture.

## Gap

Issue #13256 records the literature check. The paper has versions v1 and v2,
and v2 still states the conjecture. Its single citing work found,
arXiv:2609.39980, cites it in §8 only as a direction for future work on fusion
failures with photon loss. Reiß and van Loock (arXiv:2601.08820) give general
sufficient conditions (their Theorem 2) and construct sequences meeting them
for the quantum parity, five-qubit, standard and rotated planar surface, tree
and Steane codes; they do not assert that every connected-progenitor graph
code meets them, and their conditions 1–3 concern the success probability of
each physical Bell measurement under linear optics, which the failure model of
Proposition 3.1 does not include. The strategy here supplies, for every
connected progenitor graph, the analogue of their failure-axis sequence (Z
before the first success) and of their logical pairs (the two products of
canonical generators along the geodesic, anticommuting only at the successful
vertex). `not-found-in-searched-scope`.

## Route

1. **Order.** Attempt the physical vertices in order of decreasing graph
   distance from $e$, with failure axis Z before the first success.
2. **Geodesic.** If the first success is at $v$ with $\operatorname{dist}(e,v)
   =\ell\ge1$, fix $p_0=v$ and $p_{i+1}$ a neighbour of $p_i$ one step closer
   to $e$. The internal vertices $p_1,\dots,p_{\ell-1}$ are closer to $e$ than
   $v$, so they are attempted after $v$; from then on the axis is X on them
   and Z elsewhere.
3. **No chords.** Adjacent vertices have distances differing by at most 1, so
   $p_i\sim p_j$ forces $|i-j|=1$.
4. **Parity recursion.** If $\Gamma_U$ gave a logical failure, every vertex
   off the path has x-bit 0, so $U\subseteq\{p_1,\dots,p_\ell\}$. Each
   internal vertex and $v$ have an even number of neighbours in $U$. At $v$
   this gives $p_1\notin U$; at $p_i$ it gives $p_{i+1}\in U\iff p_{i-1}\in
   U$. Hence $U=\varnothing$, and $\Gamma_U$ is the identity at $e$.

## Falsifier

The proof would fail if an internal path vertex could be attempted before the
first success, or if a path vertex had a neighbour on the path two or more
steps away.

## Evidence

The canonical source is
`D5/S3/Quantum/Measurements/ConnectedProgenitorPerfectAdaptiveFusion.lean`.
Its public declarations are `Pauli`, `pauliI`, `genProduct`,
`IsNontrivialLogical`, `AdaptiveStrategy`, `LogicalFailure`,
`HasPerfectAdaptiveStrategy`, `claim` and `result`; the strategy of the route
is a private construction inside the module. The graph notions are Mathlib's
`SimpleGraph`, `SimpleGraph.dist` and `SimpleGraph.Connected`.
The frozen module state has statement identity
`sha256:ca17ca01c0d0c112a948de499127fec1c42d1c5d073a67b425b578dfa2079959`.
The result declaration has statement identity
`sha256:a961beb20a2b60d6e28f913ac54b0901b0964dc2d514ae9437c6d569b7ed7e23`.
The Freeze event is
`sha256:ec2a683f41fbe6c05023810864ad93e8b5fa4d71c74b79a3972599d5e072d2e5`.
It has no project-level frozen prerequisite; the module imports only Mathlib.
The proof uses only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`; no `sorry`, `native_decide`, or new axiom.

## Triage

Tier 1 external named conjecture (Discussion of a 2026 paper), preregistered
in issue #13256 before any Lean. `theorem`; resolution `proved`. The public
theorem has `proof_shape: content`; its escape witness is the parity
recursion along the chordless geodesic. Admission basis
`open-problem-resolution`; utility `none`.

What the proof shows beyond the conjecture:

- **One success suffices with only X and Z axes (proved).** The strategy never
  uses the Y axis, and the axis changes at most once per vertex, at the first
  success.
- **Order (argued; the formal proof uses one such order).** Any order of
  non-increasing distance from $e$ works by the same proof; adaptivity is
  needed only to switch the internal path vertices from Z to X after the first
  success.
- **Disconnected graphs (open here).** Section 5 of the paper remarks that a
  disconnected progenitor graph admits no perfect strategy. Whether connectedness
  therefore characterizes the codes with a perfect adaptive strategy is not
  checked or formalized here.
- **Effect on the paper.** The five-qubit example of Section 5 is now an
  instance of the general statement. The paper's open questions on the
  complexity of finding optimal non-adaptive strategies and on error-resistant
  perfect strategies are unaffected.
- **Open.** Strategies that are perfect under qubit loss or under noisy
  fusions are not addressed.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty,
priority, or the absence of an independent proof.
