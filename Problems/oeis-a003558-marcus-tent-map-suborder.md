---
slug: oeis-a003558-marcus-tent-map-suborder
bibkey: marcus2025a003558
doi: null
url: https://oeis.org/A003558
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/MarcusTentMapSuborder
---

# Marcus's tent-map cycle length and the signed suborder of two

## Problem

OEIS A003558, NAME (`%N`, verbatim):

> Least number m > 0 such that 2^m == +-1 (mod 2n + 1).

The settled COMMENT sentence (`%C`, verbatim):

> It appears that a(n) is the length of the cycle starting at 2/(2*n+1) for the map x->1 - abs(2*x-1). - _Michel Marcus_, Jul 16 2025

AUTHOR (`%A`, verbatim):

> _N. J. A. Sloane_

The offset is `%O 0,3`. The claim is read for every natural `n>0`, with
`N=2n+1`: the least positive return time of `2/N` under the tent map is
the least positive `m` such that `2^m` is congruent to `1` or `-1` modulo
`N`. The residue `-1` is written `2n` in natural congruence notation.

The exact Lean statement is:

```lean
theorem result (n : ℕ) (hn : 0 < n) :
    IsLeast {m : ℕ | 0 < m ∧ (2 ^ m ≡ 1 [MOD 2 * n + 1] ∨
      2 ^ m ≡ 2 * n [MOD 2 * n + 1])}
      (Function.minimalPeriod (tent (2 * n + 1)) 2)
```

Here `tent N k := if 2*k <= N then 2*k else 2*N - 2*k` is a natural
numerator map. For `N>0` and `k<=N`, its branches divided by `N` are
`2k/N` and `(2N-2k)/N`, exactly the two branches of the rational tent map.
Since `k<=N`, the second natural subtraction is not truncated. The orbit
invariant supplies this bound for every iterate from 2. Division by the
fixed positive `N` is injective, so numerator and rational return times
coincide. This rational interpretation is an algebraic explanation; the
kernel theorem is the displayed numerator statement.

Only the quoted Marcus sentence is settled. A003558's other comments
about Kaprekar cycles, `x^2-2` iteration, and the Kappraff-Adamson base
conjecture are not claimed. The hypothesis `0<n` excludes `n=0`, where
`N=1` and `2/N` is outside `[0,1]`.

## Motivation

The signed suborder describes the first modular power of 2 to reach
either sign of 1. The tent map folds doubling into an interval, and its
even numerator representatives turn this signed modular return into an
ordinary periodic orbit. The identity determines the whole unbounded
family of cycle lengths, rather than individual finite orbits.

## Gap

The supplied readings of 2026-09-15 report that OEIS still says
"It appears" and has no proof line for this sentence. The arXiv API
returned HTTP 429, so arXiv was not searched. OpenAlex returned 12
unrelated hits for the tent-map query; the MathOverflow and Math.SE APIs
returned zero hits, as did formal-conjectures. These external readings
are `ASSUMED-UNVERIFIED` under the no-network constraint.

The repository prior-art reading at `origin/dev = 15e0a49477` found no
tent-map or suborder declaration in D5, Library, or Problems. Pinned
Mathlib supplies the `Function.minimalPeriod` API and modular arithmetic,
but no tent-map theorem was found in the searched scope. The result is
`not-found-in-searched-scope`, not an exhaustive absence or priority claim.
Periodic rational tent-map orbits are classical dynamical-systems material.

The supplied numerical readings give zero exceptions for `1 <= n < 3000`
and zero exceptions for `1 <= n < 2000`, with 813094 exact rational
transitions in the latter probe. These bounded readings are fault-detection
evidence, not a proof of the universal statement.

Pre-registration issue #8013 is dated 2026-09-15 and precedes the probe
start according to the supplied registration reading. The problem is in
the recent-small-conjecture tier. Registration timing and external
historical openness have not been independently checked here.

## Route

1. For arbitrary `N>=2`, induction on `m` shows that `(tent N)^[m] 2`
   lies in `[0,N]`, is even, and equals either sign of `2^(m+1)` in
   `ZMod N`. The two branches of the tent map preserve these assertions.
2. For odd `N=2n+1`, the even representative in `[0,N]` of either sign
   of 2 is 2 itself: the competing representative `N-2` is odd. Since
   2 is a unit modulo `N`, cancellation identifies a return at time `m`
   with `2^m` congruent to `1` or `2n`.
3. `Nat.ModEq.pow_totient` supplies a positive return. The
   `Function.minimalPeriod` membership, positivity, and lower-bound
   interfaces give the displayed `IsLeast` assertion.

The public theorem has `proof_shape: content` and
`admission_basis: escape-witness`. Its witness is the private content
theorem `orbit_invariant`, whose unbounded induction is used in both
directions of the return equivalence. The invariant is neither an alias
nor a reformulation of the least-period conclusion. All normalization
helpers are local `have` terms; there are no direct frozen-project
dependencies. The public definition `tent` is used by this theorem.

`utility: none` applies to all declarations: the definition, unbounded
orbit induction, and least-period theorem are general symbolic mathematics,
not bounded enumeration, checker infrastructure, numeric reduction, or
a certified finite instance. Computation supplies no formal premise.

## Falsifier

A natural `n>0` for which the first positive tent-map return of `2/(2n+1)`
differs from the least positive signed modular return of 2 would refute
the identity. At the numerator level, a positive return whose power is
neither `1` nor `2n` modulo `2n+1`, or a signed modular return preceding
the first numerator return, would contradict the theorem.

## Evidence

- `lake env lean D5/S1/Recurrence/MarcusTentMapSuborder.lean`: exit 0.
  The public surface is exactly `tent` and `result`; `orbit_invariant`
  is private. The source contains no `sorry`, `native_decide`, or new axiom.
- `tools/scripts/agent/header-check.sh` on that module: exit 0; 142 lines,
  32 Lean files in the immediate directory, `generality: G` compliant.
- The scratch `#print axioms` audit: exit 0. Both `result` and the private
  `orbit_invariant` have exactly `[propext, Classical.choice, Quot.sound]`.
  The definition `tent` has no axiom dependencies. The elaborated proof
  of `result` directly references `orbit_invariant`.
- The sole direct import is `Mathlib.FieldTheory.Finite.Basic`, which
  supplies `Nat.ModEq.pow_totient` and the other required APIs transitively.
  Deleting that import through process substitution and recompiling
  exits 1, with unknown natural notation, `Even`, `ZMod`, and tactics.
- `lake env lean -Dprofiler=true -Dtrace.profiler.threshold=1000` on the
  module: exit 0. `/usr/bin/time -p` reports wall 8.76 seconds; Lean reports
  type checking 71.5 milliseconds and import 7.12 seconds. This is a
  single-file, warm-cache measurement with Lean 4.33.0 on arm64 macOS.
- Lean execution of the final `tent` for every `1 <= n < 2000`: exit 0.
  An independent exact-rational comparison: exit 0, 1999 cases, 813094
  rational transitions, and zero exceptions between the final Lean
  numerator periods, rational tent-map periods, and signed modular
  suborders. The maximum observed period is 1994 at `n=1994`. These
  bounded checks detect faults; the symbolic proof carries the universal
  conclusion.

## Triage

`theorem`; resolution `proved` for the quoted Marcus sentence with
`n>0`, subject to the explicit numerator-to-rational interpretation and
scope wall above.

## ASSUMED-UNVERIFIED

The verbatim OEIS source, external search readings, prior `n<3000`
numeric reading, and pre-registration timing are supplied facts without
independent online verification. arXiv was not searched because of HTTP
429; historical openness outside the listed search surfaces is unverified.
No exhaustive literature search or mathematical priority is claimed.
There is no separately kernel-checked rational conjugacy theorem.
Whole-tree admission, Scribe execution, rendering, and freezing are not
verified by the single-file Lean check.
