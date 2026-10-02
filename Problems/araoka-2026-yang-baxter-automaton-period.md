---
slug: araoka-2026-yang-baxter-automaton-period
bibkey: araoka2026integrable
doi: 10.1007/s11040-026-09569-9
url: https://arxiv.org/abs/2602.17148v1
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/CellularAutomata/YangBaxterAutomatonPeriod.result
---

# The Yang–Baxter cellular automata over F_{2^n} have period dividing 2^n

## Problem

A. Araoka and T. Tokihiro (arXiv:2602.17148, nlin.SI; Math. Phys. Anal. Geom.
29, 30 (2026)) build a cellular automaton over a finite field `F` from the
R-matrix `R(x, y) = (y + f(x + y), x − f(x + y))`. In characteristic 2 the
Yang–Baxter equation for `R` reduces to
`f(x) + f(x + f(y)) = f(x + f(y + f(x)))`. The automaton runs `R` along a row
of `N` cells, `R(x_i, y_{i−1}) = (x_i', y_i)` with `y_0 = b`, and the helical
boundary condition feeds `y_N` back as the next boundary value. The paper
states:

> Conjecture. The cellular automaton thus constructed over a finite field of
> order 2^n has a period that is a divisor of the order of the field.

and proves it for orders 4 and 8. Issue #11405 fixes the reading: every finite
field of characteristic 2, every bijective solution `f` of the reduced
equation, every `N`, and "period divides `q`" as `step^q = id` on the pair of
cell values and boundary value.

## Motivation

The paper's numerical tables for orders 8 and 16 show fundamental periods 1, 2,
4, 8 and 16 and no others, and the authors single out this strict periodicity
as a feature of the integrable automata: an R-matrix violating the Yang–Baxter
equation gives other periods. The frozen declaration
`D5/S3/StatisticalMechanics/CellularAutomata/YangBaxterAutomatonPeriod.result`
proves the conjecture for every order.

## Gap

Issue #11405 preregisters the reading, the route and the literature check. The
paper proves only the orders 4 and 8. INSPIRE has no record of it, and a web
search finds no follow-up. The group-theoretic step of the route is a known
fact about class-2 cycle sets (Dehornoy, Adv. Math. 282 (2015), Prop. 5.2;
Feingesicht, IJAC 34 (2024), Prop. 2.9); its application to this automaton was
not found in the searched sources.

These readings are `not-found-in-searched-scope`; they do not establish an
exhaustive worldwide literature search, priority, or the absence of an
independent answer.

## Route

1. Only the additive group is used, and `x + x = 0`. Translating `f` to
   `g(x) = f(x + a)` with `f(a) = 0` keeps the equation, and then
   `g(g(x)) = x`.
2. The involutions `L_x(y) = x + g(x + y)` fix `x` and satisfy the cycle
   identity `L_{L_x(y)} L_x = L_{L_y(x)} L_y`. The maps
   `p ↦ p L_{p⁻¹(z)}` are commuting involutions of the group `P` they
   generate, and they act transitively on `P`, so `P` is a 2-group.
3. The translations normalise `P`, so `P` and the translations generate a
   2-group. A nontrivial central element is a translation `t_u` with `u ≠ 0`
   that commutes with `g = L_0`, so `f(x + u) = f(x) + u`.
4. `R` commutes with adding elements of `{0, u}`, so one time step commutes with
   adding `{0, u}`-valued states and descends to `F/{0, u}`. By induction on the
   order, `G = step^{q/2}` satisfies `G(s) − s ∈ {0, u}` entrywise, hence
   `G(G(s)) = s` and `step^q = id`.

## Falsifier

The statement would change if the automaton were read with a non-bijective
`f`, for which the paper exhibits other periods, or with an R-matrix that does
not satisfy the reduced equation. The proof uses only the reduced equation and
bijectivity, not the full Yang–Baxter equation, so it covers every automaton of
the paper.

## Evidence

All 16816 bijective solutions of order 16 with `f(0) = 0`, and 300 random
solutions of order 32, have a nonzero `u` with `f(x + u) = f(x) + u`; sampled
automata return to their initial states after `q` steps (issue #11405).

The canonical source is
`D5/S3/StatisticalMechanics/CellularAutomata/YangBaxterAutomatonPeriod.lean`.
Its public declarations are `rmat`, `carry`, `step`, `claim` and `result`. The
frozen module state has statement identity
`sha256:f947a618fac58f588ae535ee8bb8df20a6f8475e0d407bbbc9b287c344a5161a`.
The result declaration has statement identity
`sha256:b10b29174002230d2cfc73e10370c05becae4aeed3e10a5dcb1fa3e8d3ff9c04`.
The Freeze event is
`sha256:2c5a6318dc69062e26c4aa324abe4f486714f260314c137df967ab137f9d1968`
and has no project-level frozen prerequisites. The proof uses only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`,
`native_decide`, or new axiom.

## Triage

Tier 1 conjecture from a published nlin.SI paper, preregistered in issue
#11405 before any Lean. `theorem`; resolution `proved`. The public theorem has
`proof_shape: content`; its escape witness is the translation lemma (form
(1)). Its admission basis is `open-problem-resolution`. Utility `none`.

## ASSUMED-UNVERIFIED

The published journal text was not read, so it is unverified whether the
conjecture was edited there. The bounded literature check does not establish
exhaustive worldwide novelty, priority, or the absence of an independent
answer. The Lean kernel does not authenticate the external source or its
version history.
