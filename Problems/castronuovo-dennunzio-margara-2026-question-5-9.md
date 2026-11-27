---
slug: castronuovo-dennunzio-margara-2026-question-5-9
bibkey: castronuovodennunziomargara2026orbits
doi: 10.48550/arXiv.2610.34096
url: https://arxiv.org/abs/2610.34096v1
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/CellularAutomata/CastronuovoSeeds.question_5_9
---

# Castronuovo–Dennunzio–Margara Question 5.9

## Problem

Printed p. 24 labels Question 5.9 “Simple seeds: rings versus the infinite line.”

> Can the converse of the finite-to-cyclic implication fail? More precisely, do there exist a Boolean local rule φ and an integer k for which a complete cyclic simple seed exists, but no complete simple seed on the line exists?

Definitions 2.10–2.13 require one occurrence of each projection, permit either constant symbol, and count every natural time including zero. The ring length is at least the positive rule arity. A single rule and a single positive input count must serve both clauses. [Primary source](https://arxiv.org/pdf/2610.34096v1#page=24)

## Motivation

Proposition 2.14 transfers completeness of a simple line seed to a simple ring seed. The reverse transfer is the tier-1 question. It tests whether winding around a finite ring allows a simple seed to realize more functions than any simple line seed can realize. [Preregistration #34949](https://github.com/the-omega-institute/trureturing/issues/34949)

## Gap

The preregistration reports a bounded search of the versioned arXiv record, title and authors, citation indexes, MathDB, formal-conjectures and the project’s Problems and issue index. That search found no earlier settlement of this question. Worldwide priority remains unverified. [Preregistration #34949](https://github.com/the-omega-institute/trureturing/issues/34949)

## Route

Use two inputs and the rule φ(a,b,c,d) = ¬a ∧ ((b ∧ ¬c) ∨ d) at offsets −1, 0, 1, 2. The ring seed (X,Y,0,0,1) on ℤ/5ℤ contains each projection exactly once. Its first six rows contain all sixteen Boolean-function masks. For every simple line seed, the parity of the unique X site fixes the direction of the checkerboard comparison when X changes. The rule preserves that comparison at every time, so the order in X at any output site has a direction independent of Y. XOR reverses that direction as Y changes.

## Falsifier

The constructed witness would fail if a mask were absent from the first six ring rows, if the seed failed the ring-length or simplicity condition, or if a legal simple line seed realized XOR for the same rule. A compilation that used different rules for the two clauses would fail source fidelity.

## Evidence

`question_5_9` proves the existential statement with `StronglyCyclicUniversal φ k ∧ ¬ StronglyUniversal φ k`. Its standard axiom closure is `propext`, `Classical.choice` and `Quot.sound`. The public result records exact author replay and the all-sites, all-times obstruction. [Public result](https://github.com/the-omega-institute/trureturing/issues/34949#issuecomment-7226662505)

## Triage

`theorem`. The affirmative answer separates simple rings from simple finite-background line seeds.

## ASSUMED-UNVERIFIED

The preregistration documents the literature search scope. Global priority and canonical activation are pending.
