---
bibkey: leanpool2026nbccancellation
authors: "ukiyois; OpenCode agent sessions"
year: 2026
title: "Finite-matroid broken-circuit cancellation"
doi: null
url: "https://github.com/LeanPool/lean-pool/blob/d7dcd3c02cf0e220932dd033d5cc2353933d754b/LeanPool/HardSphereNBC/NBCMatroid.lean"
claim: "The immutable source supplies the least circuit-completer toggle, its stability and span-preservation, the sign-reversing involution on bad spanning subsets, and the surviving NBC-base cancellation identity."
strata_touched:
  - D5/S3/Combinatorics/Matroids/BrokenCircuitCancellation
license: Apache-2.0
triage: anchor
---
# Finite-matroid broken-circuit cancellation source

## Verified locator

LeanPool/lean-pool at immutable revision `d7dcd3c02cf0e220932dd033d5cc2353933d754b`,
`LeanPool/HardSphereNBC/NBCMatroid.lean`, SHA-256
`52db754a8119adb22a04682e30f3936c39ea90c29e75b33876e2c7b7ed28e861`:
https://github.com/LeanPool/lean-pool/blob/d7dcd3c02cf0e220932dd033d5cc2353933d754b/LeanPool/HardSphereNBC/NBCMatroid.lean

## Reused result

The source proves cancellation over a finite ambient carrier for an arbitrary matroid ground `M.E`.
It defines the least circuit-completing element using the circuit maximum convention, proves witness
stability under toggling, preserves spanning, and applies the sign-reversing fixed-point-free
involution to the bad spanning subsets. The no-broken-circuit spanning survivors are proved to be
actual bases. This delivery ports that proof mechanism to the pinned Lean and presents the endpoint
as the integer-power identity over the explicit ground-contained actual NBC-base filter.

The port is retired when the pinned Mathlib supplies an equivalent full finite-matroid cancellation
result with the accepted standard axiom closure.
