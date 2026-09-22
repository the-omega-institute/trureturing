---
slug: joshi-rust-fibonacci-map-bound
bibkey: joshirust2025monochromatic
doi: 10.1016/j.tcs.2025.115391
url: https://arxiv.org/html/2501.05830v2
triage: theorem
motivation_gids:
  - D5/S1/Words/Mechanical/MechanicalGoldenBridge
---

# Fibonacci-word MAP maximum

## Problem

Joshi and Rust, *Monochromatic arithmetic progressions in the Fibonacci,
Thue-Morse, and Rudin-Shapiro words*, arXiv:2501.05830v2, Theoretical
Computer Science 1050 (2025), 115391, Conjecture 4.24:

> For all d >= 1, (A(d)-1)/d < sqrt(5)/tau.

Here `tau=(1+sqrt(5))/2` and `A(d)` is the global maximum positive length
of a monochromatic arithmetic progression of difference `d` in the
zero-indexed infinite Fibonacci fixed point `0 -> 01, 1 -> 0`. Both symbols
and every nonnegative starting position are included.

## Motivation

The source gives exact expressions for `A(d)` in the small- and large-step
regimes (Theorems 4.6 and 4.15), but leaves this strict uniform comparison
with the golden ratio as Conjecture 4.24.

## Gap

The strict inequality must hold at every positive difference, including
the boundary `d=1` and arbitrary starts. A real estimate alone does not
establish strictness at the nearest integer threshold.

## Route

The repository's infinite `goldenWord` is read through the golden mechanical
letter at the `i+1` fractional coordinate. In the small-step regime the
opposite letter's interval prevents wraparound; in the large-step regime
two successive jumps decrease the position within alternating clusters.
The quadratic norm of an integer approximation to `d*tau` gives a positive
integer lower bound. Integer spacing sharpens the small-step real estimate;
the large-step estimate applies for `d>=7`, with the remaining six
denominators resolved by exact floor identities and fractional windows.
Lengths are bounded and a length-one progression exists, so their supremum
is an attained global maximum rather than a formula-defined surrogate.

## Falsifier

Any positive difference, start, letter and finite monochromatic progression
whose length violates the strict bound would contradict the result. A
mismatch between the repository's Boolean letters and the source's
zero/one indexing would instead refute the source correspondence.

## Evidence

- Formal source: `D5/S1/Words/FibonacciMapBound.lean`.
- Definition: `goldenMAPMaximum`; conclusion: `result`.
- The result's axiom closure is `propext`, `Classical.choice`, `Quot.sound`.

## Triage

`theorem`. The result addresses the literal global Conjecture 4.24 and no
claim about other words or asymptotic sharpness.

## ASSUMED-UNVERIFIED

The bounded source audit through 17 September 2026 found no later qualifying
proof or refutation; exhaustive publication priority is unverified.
