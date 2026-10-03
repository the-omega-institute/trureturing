---
slug: marton-2023-double-cglmp-one-bit-bound
bibkey: marton2023onebit
doi: 10.48550/arXiv.2308.10771
url: https://arxiv.org/abs/2308.10771v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/DoubleCglmpOneBitBound.result
---

# The one-bit bound of the double CGLMP game

## Problem

I. Márton, E. Bene, P. Diviánszky and T. Vértesi (arXiv:2308.10771, quant-ph;
npj Quantum Information 10, 79 (2024)) look for Bell-type inequalities that
local hidden variables cannot saturate even with one bit of communication.
With `CGLMP_d = P(A₀ ≥ B₀) + P(A₀ ≤ B₁) + P(A₁ < B₀) + P(A₁ ≥ B₁)` and two copies
played in parallel, they state:

> The one-bit bound L1bit(CGLMP_d^{⊗2}) = 12 in the last column is verified by
> the branch-and-bound algorithm up to d = 10. We conjecture that this is the
> exact bound for any d ≥ 2.

For the truncations to the inputs `{00, 01, 11} × {00, 01, 11}` and
`{00, 01, 11} × {00, 11}` they give "the conjectured local bound" 7 and 4,
"which we verified up to d = 20".

Issue #11276 fixes the reading. Local behaviours follow eq. (P_LHV): the hidden
variable has an arbitrary probability distribution on `ℝ`, and the responses are
measurable conditional distributions. One-bit behaviours follow eq.
(P_LHV1bit), with a measurable bit `l(X, λ)`; both directions of communication
are included, as the paper lists the game as bidirectional. Each bound is the
greatest value of the Bell expression over its class.

## Motivation

`Q(CGLMP_8^{⊗2}) > 12`, so if the one-bit bound is 12 the double CGLMP game gives
a four-input Bell-type inequality with one bit of communication that quantum
correlations violate; the truncations do the same with three inputs. The frozen
declaration `D5/S3/Quantum/Information/DoubleCglmpOneBitBound.result` proves the
three bounds for every `d ≥ 2`.

## Gap

Issue #11276 preregisters the reading, the route and the literature check. The
paper has one arXiv version; its npj text states the same conjecture. INSPIRE
lists 3 citing records (2026-09-29); none proves the bounds. arXiv queries on
CGLMP with communication and one-bit Bell bounds since 2023-08 found no proof.

These readings are `not-found-in-searched-scope`; they do not establish an
exhaustive worldwide literature search, priority, or the absence of an
independent answer.

## Route

1. In one copy, inputs `U, V` of Alice with bits 0, 1 and `W, Z` of Bob with bits
   0, 1: the four winning conditions would give
   `α_U ≤ β_Z ≤ α_V < β_W ≤ α_U`, so in every rectangle `{U, V} × {W, Z}` on
   which Bob answers alike some cell is lost.
2. A kernel-checked count over the Boolean patterns of won cells: three inputs
   of one party with the same message lose at least four of their twelve cells,
   two lose at least two of their eight. Splitting the inputs by the message,
   at most 12 of the 16 cells are won; the truncations win at most 7 and 4.
3. For a fixed hidden value the Bell expression is linear in each response, so
   best outputs do not decrease it; integrating gives the bounds for the
   classes. Point strategies with outputs 0 and 1 attain them for every `d`.

## Falsifier

The answer would change if the one-bit class allowed Bob's response to depend on
Alice's input other than through one bit, or if the Bell expression weighted the
sixteen input pairs unequally.

## Evidence

Exhaustive search over deterministic strategies (issue #11276) gives one-bit
bound 12 in both directions and local bound 10 for `d = 2, 3`, and the
truncation bounds 7 and 4 for `d = 2, 3, 4`. Weakening the condition `a < b` to
`a ≤ b` raises the values to 16, 9 and 6.

The canonical source is
`D5/S3/Quantum/Information/DoubleCglmpOneBitBound.lean`. Its public declarations
are `Inp`, `copyWins`, `wins`, `bell`, `IsResponse`, `IsLocal`, `IsOneBitAB`,
`IsOneBitBA`, `symInputs`, `asymInputs`, `claim` and `result`. The frozen module
state has statement identity
`sha256:717d77a196e7af507f2e049ba79828dac951776dcd07d2632d36c6f9d7f99386`.
The result declaration has statement identity
`sha256:9d205189f43fc332561288cc89563025cd579261fcf1d889b59c65d4f773f368`.
The Freeze event is
`sha256:900c21fffc67af17929ae0e97d45b5833688497b023b3e127356c41547e9d885`
and has no project-level frozen prerequisites. The proof uses only the standard
axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`,
`native_decide`, or new axiom.

## Triage

Tier 1 external named conjecture and two conjectured bounds, preregistered in
issue #11276 before any Lean. `theorem`; resolution `proved`. The public theorem
has `proof_shape: content`: the order cycle, the rectangle counts and the
derandomisation are proved in the module. Its escape witness is form (2), and
its admission basis is `open-problem-resolution`. Utility `none`: the statement
holds for every `d ≥ 2` and every hidden-variable model.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty,
priority, or the absence of an independent answer. The Lean kernel does not
authenticate the external source or its version history.
