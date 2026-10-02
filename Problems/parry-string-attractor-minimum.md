---
slug: parry-string-attractor-minimum
bibkey: gheeraertromanastipulanti2023attractors
doi: null
url: https://arxiv.org/abs/2302.13647v2
triage: theorem
motivation_gids:
  - D5/S1/Words/Powers/WordPower
---

# Original cyclic-morphism string-attractor minimum

## Problem

For k >= 2, let c be a length-k vector of natural coefficients with
c(0) >= 1 and c(k-1) >= 1. Set d to c with the last entry decreased by
one and assume d is lexicographically at least every cyclic rotation,
allowing equality. The original substitution sends a < k-1 to c(a)
zeros followed by a+1, and sends k-1 to c(k-1) zeros.

Let u be its fixed point starting with zero and U(n) the length of the
n-th iterate of that singleton. Conjecture 42 states that for every m >= 1,
the prefix of length m has minimum attractor size i+1 when
0 <= i <= k-2 and U(i) <= m < U(i+1), and size k when m >= U(k-1).
The minimum ranges over every position subset; each nonempty factor needs
an equal occurrence wholly inside the same prefix crossing a selected
original position.

## Evidence

The preregistration is [issue 11754](https://github.com/the-omega-institute/trureturing/issues/11754).
The exact source is Gheeraert–Romana–Stipulanti, arXiv:2302.13647v2,
Conjecture 42, under the original working hypotheses and Definition 2.
The unrestricted attractor definition opens Section 4; its one-based positions
correspond to Lean zero-based positions by adding one.

## Motivation

The existing word-power API reads repeated literal blocks modulo their original
length. This makes the source morphism recurrence a natural setting for
constructing small hitting sets of original factor occurrences.

## Gap

The paper-level endpoint intervals leave residual prefixes below the next
canonical interval. Those prefixes require a bounded actual replacement window
through the full original coefficient recurrence. Published supplier statements
are not accepted mathematical premises.

## Route

The Lean result uses the literal morphism and unrestricted minimum. Nesting
and U(n) >= n+1 establish fixed-point-prefix semantics. Weak cyclic
maximality proves all-level periodic interiors. Canonical endpoint intervals,
a finite full-k block scan and exact window transport supply the upper bound;
singleton factors supply the unrestricted lower bound.

## Falsifier

A valid counterexample must use the original coefficients and letters and
one positive prefix length whose unrestricted minimum violates the stated
value. A coded-word, primitive-only, assumed-periodicity or finite-box result
does not settle this problem. Equal rotations, proper powers, zero middle
coefficients, empty residual intervals and r=0 remain in scope.

The original authors retain credit for the conjecture. The mathematical
implementation claims no worldwide novelty or independent review status.

## Triage

`theorem`. The complete quantified statement is the target of the retained
Lean result; required independent review, registration admission and canonical
publication remain separate obligations.

Proved in the implementation: weak cyclic maximality controls every iterate
interior, and an actual suffix window transfers the missing residual factors.
The unrestricted singleton lower bound makes the constructed upper bounds
sharp. The finite-word suppliers are owned by
`D5/S1/Words/Attractors/FiniteWordAttractors`, the coherent-prefix induction
and residual scan by `D5/S1/Words/Attractors/PeriodicPrefixAttractors`, and
the literal morphism bridges and sole full result by
`D5/S1/Words/Attractors/CyclicMorphismAttractorMinimum`. The same scan treats equal rotations and proper powers without a
primitive-root assumption. No extension beyond the stated coefficient
hypotheses is claimed.

## ASSUMED-UNVERIFIED

The supplied preregistration and bounded prior-art conclusions do not certify
worldwide priority or the current state of every external source. The source
version is arXiv:2302.13647v2; later publication variants are outside this claim.
