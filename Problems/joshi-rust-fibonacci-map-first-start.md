---
slug: joshi-rust-fibonacci-map-first-start
bibkey: joshirust2025monochromatic
doi: 10.1016/j.tcs.2025.115391
url: https://arxiv.org/html/2501.05830v2
triage: theorem
motivation_gids:
  - D5/S1/Words/Mechanical/MechanicalGoldenBridge
  - D5/S1/Words/FibonacciMapBound
  - D5/S1/Scale/Fibonacci
---

# First longest progressions at Fibonacci differences

## Problem

Joshi and Rust, *Monochromatic arithmetic progressions in the Fibonacci,
Thue-Morse, and Rudin-Shapiro words*, Theoretical Computer Science 1050
(2025), 115391, arXiv:2501.05830v2, Conjecture 3.19:

> i(F_(2n+1)) = F_(2n+3) - 2, and i(F_(2n)) = F_(4n) - 1.

The quantifier is every natural `n >= 1`, as independently clarified in
the author's A364648 comment. Here `F_0=0`, `F_1=1`. The word is the
zero-indexed fixed point `010010100100101...` of `0 -> 01, 1 -> 0`.
For a positive difference `d`, `A(d)` is the global maximum of positive
lengths over every nonnegative start and both symbols; `i(d)` is the least
start attaining that maximum, again allowing either symbol. Definitions
2.2, 2.3 and 2.5 supply these conventions.

## Motivation

The mechanical bridge identifies the actual substitution word with the
golden rotation at index `j+1`. The existing maximum definition and Cassini
identity give independent anchors for the first-start problem. The source
explains that its Walnut method cannot handle the variable multiplication
needed when `A(F_m)` grows with `m`.

## Gap

Finding a longest progression at the displayed start does not exclude an
earlier progression of either symbol. A supremum formula also needs a
bounded length set and a genuine attaining start. The even boundary `m=2`
has step exactly equal to the smaller symbol-window length.

## Route

Write `r=1/tau`, `eps=r^m`, and use the open true-letter interval `(r^2,1)`.
Cassini's determinant expresses a denominator and its positive forward or
backward error in integral Fibonacci coordinates. An error below `eps`
forces one coordinate at least one and the other nonnegative; a positive
second coordinate forces denominator at least `F_m+F_(m+1)=F_(m+2)`.

The maximum length is `F_(m-2)+F_m` for odd `m`, and one more for even `m`.
The endpoint-aware no-wrap argument bounds all runs, makes every false
run strictly shorter, and characterizes the starts of maximum-length
runs. Signed golden Fibonacci identities give exact span products.
For odd `m`, the candidate has positive orbit index `F_(m+2)-1`; earlier
maximal phases translate by one rotation to a positive error below `r^m`.
For even `m`, the candidate has index `F_(2m)`; earlier phases have
backward error below `r^(2m-1)`, contradicting the preceding even record
`r^(2m-2)`. Taking the infimum of the nonempty start set proves both
equations without extra hypotheses.

## Falsifier

A positive `n` with a different least start for either displayed difference
refutes the literal conjunction. An earlier false-symbol run attaining
the maximum, an unattained or unbounded supposed maximum, or a mismatch
in the `j+1` phase bridge would invalidate the mathematical correspondence.

## Evidence

- Formal source: `D5/S1/Words/FibonacciMapFirstStart.lean`.
- Public definition: `goldenMAPFirstStart`; exact conjunction: `result`.
- The source proves the finite one-sided orbit exclusions, boundedness,
  attainment, maximum equality and least-start exclusions for all `n>=1`.
- The axiom closure is `propext`, `Classical.choice`, `Quot.sound`.
- Preregistered exact target: https://github.com/the-omega-institute/trureturing/issues/8451.
- Exact source anchor: https://arxiv.org/html/2501.05830v2#S3.Thmtheorem19.
- Library-first searches covered repository D5, pinned Mathlib
  `db584cd6d46c92f209a44c0f1c829460d327499d`, and bounded third-party
  Lean searches. Loogle `Nat.fib, Int.fract` returned zero results;
  Fibonacci/golden best-approximation searches found no exact one-sided
  Fibonacci record statement. Generic continued-fraction APIs did not
  directly supply the required indexed inequalities. Cassini, the
  mechanical word bridge and the parity fractional-part formulas are reused.

## Triage

`theorem` describes the exact formal statement, not final admission or
publication status. Independent review, the final resolution attachment,
canonical freeze, required CI and ordinary merge remain required; this
dossier does not claim they have occurred.

## ASSUMED-UNVERIFIED

The bounded literature audit and author-page checks through 17 September
2026 found no later proof or refutation. Exhaustive publication priority
is unverified. The thesis reading was oracle-reported, not independently
verified by caller HTTP access, which returned 403. Source-to-formal
faithfulness and the proof classification still require independent review.
