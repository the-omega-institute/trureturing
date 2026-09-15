---
slug: oeis-a002000-bala-cubic-three-adic-congruence
bibkey: bala2022a002000
doi: null
url: https://oeis.org/A002000
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/BalaCubicThreeAdicCongruence
---

# Bala's cubic recurrence and its growing three-adic congruence

## Problem

OEIS A002000, NAME (`%N`, verbatim):

> a(n+1) = a(n)*(a(n)^2 - 3) with a(0) = 7.

The settled FORMULA line (`%F`, verbatim), inside Peter Bala's Nov 15 2022
`(Start)` ... `(End)` block:

> Conjecture: a(n+1) == a(n) (mod 3^(n+r+2)) for n >= r.

AUTHOR (`%A`, verbatim):

> _N. J. A. Sloane_

The offset is `%O 0,1`. Both `n` and `r` range over the natural numbers,
including zero, and the only hypothesis is `r <= n`. The sequence has
values in the integers and is defined by the NAME recurrence. Congruence
means that `3^(n+r+2)` divides the integer difference `a(n+1)-a(n)`.

The exact Lean statement is:

```lean
theorem result (n r : ℕ) (hr : r ≤ n) :
    (3 : ℤ) ^ (n + r + 2) ∣ a (n + 1) - a n
```

Only the Conjecture line is settled, for every `n` and every `r <= n`.
The block's Lucas representation, 3-adic limit, and product formula are
not claimed. In particular, `a` is not defined through Lucas numbers.

## Motivation

The conjecture gives an increasing power of 3 shared by consecutive
terms of a cubic recurrence. The shift `a(n)+2` makes its two-power gain
visible and accounts for all the moduli indexed by `r <= n`. The result
describes the entire unbounded family of indices.

## Gap

Readings of 2026-09-15: OEIS still marks the settled line `Conjecture`. OpenAlex returned four hits for `A002000`, all
unrelated by title. The Math.SE and MathOverflow APIs each returned zero
hits, as did formal-conjectures. The arXiv API returned HTTP 429, so arXiv
was not searched. These external readings are `ASSUMED-UNVERIFIED`.

Repository prior art at `origin/dev = fe47b6c24b`: the search
found no A002000 declaration in D5, Library, or Problems. Pinned Mathlib
provides `padicValNat`, `Nat.ModEq`, `pow_dvd_pow`, and `Dvd.dvd.mul_left`;
no such sequence or complete congruence was found in the searched scope.
The result is `not-found-in-searched-scope`, not an exhaustive literature
or priority claim. Bala's own block gives only the weaker `mod 3^(n+1)`
congruence through the Gauss congruences for Lucas numbers; no proof of
the `3^(n+r+2)` strengthening was found.

Exact-integer checks give zero exceptions for `0 <= n <= 12`,
`0 <= r <= n` (91 pairs). On this range,
`v_3(a(n+1)-a(n)) = v_3(a(n)+2) = 2n+2` exactly, so the conjecture's
modulus is sharp at `r=n` for the tested indices. These are bounded
observations; the universal exact valuation equalities are not claimed.

Pre-registration issue #8091 (created 2026-09-15T12:59:39Z) precedes the
first proof attempt (2026-09-15T13:00:30Z). The problem is in the
recent-small-conjecture tier. External historical openness beyond the
listed search surfaces has not been independently checked here.

## Route

1. Induction proves `3^(2n+2) ∣ a(n)+2`. The base is `a(0)+2=9`.
   For the step, `a(n+1)+2=(a(n)-1)^2(a(n)+2)`, and the induction
   hypothesis implies `3 ∣ a(n)+2`, hence `3 ∣ a(n)-1`. Squaring the
   latter factor supplies the two additional powers of 3.
2. The factorization `a(n+1)-a(n)=a(n)(a(n)-2)(a(n)+2)` transfers the
   invariant to divisibility of the difference by `3^(2n+2)`.
3. The bound `r <= n` gives `n+r+2 <= 2n+2`; `pow_dvd_pow` and
   divisibility transitivity give the stated congruence.

The public theorem has `proof_shape: content` and
`admission_basis: escape-witness`. Its witness is the private content
theorem `a_plus_two`, whose unbounded induction supplies a quotient for
`a(n)+2`. That quotient is used to construct the divisor witness for the
difference, so the invariant is on the live proof path. It is distinct
from the difference-divisibility conclusion. All bare instantiations and
factorizations remain local `have` terms or inline rewrites. There are no
direct frozen-project dependencies; the public definition `a` is used
by `result`.

`utility: none` applies to every declaration: the recurrence definition,
unbounded invariant, and universal congruence are symbolic mathematics,
not bounded enumeration, checker infrastructure, numeric reduction, or
a certified finite instance. Numerical checks supply no formal premise.

## Falsifier

A natural pair `n,r` with `r <= n` for which
`(a(n+1)-a(n)) % 3^(n+r+2) != 0`, using exact integer recurrence values,
would refute the conjecture. The boundary pair `n=r=0` is included:
`a(1)-a(0)=315` is divisible by 9.

## Evidence

- `lake env lean D5/S1/Recurrence/BalaCubicThreeAdicCongruence.lean`:
  exit 0. The public surface is exactly `a` and `result`; `a_plus_two`
  is private. The source contains no `sorry`, `native_decide`, or new axiom.
- `tools/scripts/agent/header-check.sh` on that final module: exit 0;
  53 lines, 36 Lean files in the immediate directory, `generality: G`
  compliant. The seven-line header has a 75-character digest payload
  on an 89-character physical line.
- Scratch `#print axioms` audit: exit 0. The axiom closures are
  `[propext]` for `a`, `[propext, Quot.sound]` for private `a_plus_two`,
  and exactly `[propext, Classical.choice, Quot.sound]` for `result`.
  The elaborated proof directly uses `a_plus_two` to choose the quotient
  in its divisibility witness. The inhabited-domain and satisfiable-bound
  examples `example : ℕ := 0` and
  `example : (0 : ℕ) ≤ 0 := Nat.le_refl 0` also elaborate with exit 0.
- Deleting each direct import from the final module by process
  substitution and recompiling gives the following readings:

  | Direct import | Deletion exit | Diagnostic |
  | --- | --- | --- |
  | `Mathlib.Algebra.Ring.Divisibility.Basic` | 1 | Unknown identifier `dvd_sub` |
  | `Mathlib.Tactic.Ring` | 1 | Unknown tactics and unsolved goals |

  No other direct import is needed; the remaining facilities arrive
  transitively through these two imports.
- `lake env lean -Dprofiler=true -Dtrace.profiler.threshold=1000` on the
  final module: exit 0. `/usr/bin/time -p` reports 10.21 seconds wall;
  Lean reports type checking 22.4 milliseconds and import 4.52 seconds.
  This is a warm-cache, single-file reading with Lean 4.33.0 on arm64
  macOS, based on worktree HEAD
  `9761d64157a949aeb1e846850b4334b397b426cb` plus this module.
- Lean execution of the final definition: exit 0. An independent
  exact-integer Python check: exit 0. Both evaluate through
  `a(13)`, begin `7, 322, 33385282`, and find zero exceptions for all
  91 pairs `0 <= n <= 12`, `0 <= r <= n`. Comparing their 13 valuation
  rows: exit 0; both valuations equal `2n+2` at every tested index.
  These bounded checks detect faults; induction proves the unbounded
  congruence.

## Triage

`theorem`; resolution `proved` for the quoted Conjecture line, with the
integer recurrence and scope wall above.

## ASSUMED-UNVERIFIED

The verbatim OEIS source, external search readings, historical repository
prior-art reading at `fe47b6c24b`, and pre-registration chronology were
read on 2026-09-15 and are `ASSUMED-UNVERIFIED` here. arXiv was not
searched because of HTTP 429; historical openness outside the listed
search surfaces remains unverified. No exhaustive literature search or
mathematical priority is claimed. The unbounded exact valuation
equalities, Lucas representation, 3-adic limit, and product formula are
not formal conclusions here.
