---
slug: castronuovo-dennunzio-margara-2026-question-5-6
bibkey: castronuovodennunziomargara2026orbits
doi: 10.48550/arXiv.2610.34096
url: https://arxiv.org/abs/2610.34096v1
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/CellularAutomata/CastronuovoSeeds.question_5_6
---

# Castronuovo–Dennunzio–Margara Question 5.6

## Problem

Printed p. 24 labels Question 5.6 “Simple versus unrestricted completeness.”

> Does there exist a Boolean local rule and an integer k which is k-universal but not strongly k-universal?

Both predicates are for finite-background line seeds in Definitions 2.10–2.13. The positive clause allows repeated projections. The negative clause ranges over all simple line seeds of the same positive input count for the same local rule. [Primary source](https://arxiv.org/pdf/2610.34096v1#page=24)

## Motivation

A complete unrestricted line seed can use repeated copies of projections to realize functions missing from every simple line orbit. This tier-1 question admits any positive local rule arity. [Preregistration #34950](https://github.com/the-omega-institute/trureturing/issues/34950)

## Gap

The preregistration reports a search of the versioned arXiv and citation records and the project’s Issues and Problems collections. It found no matching resolution and distinguishes the elementary-rule question numbered 5.3. Worldwide priority remains unverified. [Preregistration #34950](https://github.com/the-omega-institute/trureturing/issues/34950)

## Route

Use two inputs and the rule φ(a,b,c,d) = ¬a ∧ ((b ∧ ¬c) ∨ d) at offsets −1, 0, 1, 2. Put four copies of (X,Y,0,0,1) on the inclusive interval [−5,14], beginning at −5 and with X at 0, and put constant zero elsewhere. The light cone [i−t,i+2t] is inside that interval for each site 0 ≤ i ≤ 4 and time 0 ≤ t ≤ 5. The line agrees there with the periodic extension of the five-ring seed. Periodic extension commutes with the update, so this one line seed realizes all sixteen letters. The checkerboard comparison excludes XOR from every simple line orbit, for either initial background.

## Falsifier

The proposed finite witness would fail if its phase or interval missed a checked light cone, if any mask were absent, or if a simple line seed realized XOR for the same rule. The source-fidelity check requires unrestricted and simple seed families on the integer line in the two respective clauses.

## Evidence

`question_5_6` proves the existential statement with `Universal φ k ∧ ¬ StronglyUniversal φ k`. Its standard axiom closure is `propext`, `Classical.choice` and `Quot.sound`. The public result records exact author replay, the zero-background witness and the shared obstruction. [Public result](https://github.com/the-omega-institute/trureturing/issues/34950#issuecomment-7226662491)

## Triage

`theorem`. The affirmative answer separates unrestricted completeness from simple completeness on the integer line.

### What the settlement shows

- **Proved.** The twenty-site word realizes the finite set of ring letters on the zero-background line. Repeating the projections is allowed in the positive clause. The negative clause follows from the uniform signed order on every simple line orbit, for either background. The result is `D5/S3/StatisticalMechanics/CellularAutomata/CastronuovoSeeds.question_5_6`.
- **From Proposition 2.14.** An unrestricted complete ring seed can be transferred to the line by retaining the cones of finitely many realizing sites. The companion result `D5/S3/StatisticalMechanics/CellularAutomata/CastronuovoSeeds.question_5_9` supplies a simple complete ring for this same rule and input count. Its transfer yields an unrestricted line witness, so the two conclusions concern the same failure of simple completeness on the line. [Proposition 2.14](https://arxiv.org/pdf/2610.34096v1#page=11)
- **Open here.** Minimality of the arity and witness length is unverified. This construction leaves the elementary-rule question 5.3 and the general decision problems in Question 5.7 open.

## ASSUMED-UNVERIFIED

The preregistration documents the literature search scope. Global priority remains unverified.
