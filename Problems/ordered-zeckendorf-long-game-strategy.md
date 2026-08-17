---
slug: ordered-zeckendorf-long-game-strategy
bibkey: bortnovskyi2025ordered
arxiv_id: 2508.20222
triage: theorem
motivation_gids:
  - D5/S0/Conventions/WDigits
  - D5/S1/Digit/Raw
  - D5/S1/Digit/Carry
  - D5/S1/Digit/Normalize
  - D5/S0/Rewriting/NewmanConfluence
  - D5/S0/Rewriting/NormalFormFunction
---

# Optimality of the Ordered Zeckendorf Long Game Strategy

## Problem

A state is an ordered list of Fibonacci numbers. The game starts with `n` copies
of `F_1`. Legal adjacent moves are `(F_i, F_{i+1}) -> F_{i+2}`;
`(F_1, F_1) -> F_2`; `(F_i, F_i) -> (F_{i-2}, F_{i+1})` for `i > 2`;
`(F_2, F_2) -> (F_1, F_3)`; and switching an inversion `(F_i, F_j) -> (F_j, F_i)`
when `i > j`.

The Long Game Strategy uses the priority: all switch moves in any order, combine
adjacent ones from the left, split from the right, then merge from the left.

Conjecture 1.7, quoted from arXiv:2508.20222v2:

> "The LGS has the longest game length."

Status statement, quoted from the same version:

> "The longest-game strategy described in Conjecture 1.7 is supported by
> empirical simulations. However, a rigorous proof establishing its optimality
> remains an open problem."

Proposed formalization, after importing the five moves exactly:

```text
∀ n, ∀ g, IsLGSRun n g ->
  Terminal g.last ∧
  ∀ h, LegalTerminalRun n h -> h.length ≤ g.length
```

This universal form is appropriate only if the paper's "switch moves (in any
order)" is intended to give the same LGS length for every switch ordering.
Otherwise use an explicit deterministic tie-breaker or an existential maximizing
LGS run.

The paper says the conjecture is backed by exhaustive simulations rather than a
proof. In its broader exact game-tree analysis it also states:

> "Due to the combinatorial explosion in the number of game states and legal
> move sequences, a full resolution of the winner for \\(n>25\\) was
> computationally infeasible."

That second quote concerns winner computation, not directly Conjecture 1.7, but
it identifies the same state-space obstacle. For length, the paper proves only
upper and lower asymptotics and a structural lemma about repetitions under LGS.

## Motivation

- Erasing order maps a game state to `RawDigits`. Each merge and split move
  preserves Fibonacci value and is closely related to a frozen carry step;
  switch moves erase to the identity.
- The frozen normalizer proves termination and unique canonical output for its
  own oriented carry system. This explains the shared terminal Zeckendorf state,
  but confluence intentionally forgets path lengths.
- The new content is an extremal refinement of rewriting: among ordered
  value-preserving paths from `[F_1,...,F_1]` to the sorted normal form, LGS
  should maximize length.

## Gap

- `RawDigits` is a multiplicity map and loses order; no ordered list state or
  inversion count exists.
- Frozen carry orientation is not identical to the paper's bidirectional
  merge/split game.
- Newman confluence and normal-form uniqueness say nothing about longest paths.
- LGS contains a tie phrase "switch moves (in any order)" that must be resolved
  before a Lean proposition is exact.

## Route

1. Define ordered index lists and the five legal moves; prove value preservation
   and the forgetful map to `RawDigits`.
2. Port the paper's strictly decreasing monovariant to obtain a finite DAG
   independently of frozen normalization.
3. Define `height(S)` as the longest remaining path to terminal. It satisfies a
   Bellman recursion on the finite DAG.
4. Prove local exchange lemmas matching LGS priority: an inversion swap can be
   commuted before any non-switch without decreasing remaining height; leftmost
   `F_1` merge dominates other merge choices; rightmost split dominates other
   splits.
5. Use the paper's at-most-one-higher-index-repetition state classification to
   make the split exchange finite. A successful proof shows the LGS move is
   always an argmax successor in the Bellman recursion.
6. Prove switch-order independence as a separate lemma; if false, tighten the
   conjecture to the paper's intended deterministic interpretation and record
   the counterexample.

## Falsifier

A complete certificate consists of a smallest `n`, an exact legal terminal LGS
run `g`, and another exact legal terminal run `h` with `length h > length g`. If
switch ordering changes LGS length, two LGS runs with unequal lengths falsify
the universal proposed formalization even if one remains globally maximal.

## Evidence

Construct a memoized exact DAG for `n <= 30`:

1. canonicalize states only by the ordered Fibonacci-index tuple; do not
   quotient by multiplicity;
2. compute exact `height(S)` and retain a maximizing successor witness;
3. enumerate every LGS tie choice and compare its length to `height(start_n)`;
4. emit, for each state reached by LGS, whether its chosen move is
   height-maximizing;
5. when a priority exchange first fails locally, save both suffix paths even if
   the global conjecture still holds.

This extends the paper's simulation into proof-certificate-shaped data and
directly probes the formal ambiguity.

## Triage

`theorem`. The state space is finite and terminating, and the repository has the
value/carry/normal-form backbone; the likely proof is a finite family of
exchange lemmas rather than a new analytic theory.

## ASSUMED-UNVERIFIED

- All permitted switch orders in LGS have equal length, or the authors intended
  a deterministic completion not explicit in the quoted definition.
- The paper's game moves correspond cleanly enough to frozen carry identities to
  reuse value proofs.
- The at-most-one-repetition lemma suffices to close every local optimality
  branch.
- Whether Conjecture 1.7 was resolved after arXiv v2 is unverified; novelty of
  the exchange-lemma route is unassessed.
