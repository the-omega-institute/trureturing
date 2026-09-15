---
slug: oeis-a002487-adamson-stern-farey-inverse
bibkey: adamson2023a002487
doi: null
url: https://oeis.org/A002487
triage: theorem
motivation_gids:
  - D5/S3/PrimeForms/SternBrocot/AdamsonSternFareyInverse
---

# Stern values invert the next Farey-tree numerator

## Problem

OEIS A002487, NAME (`%N`, verbatim):

> Stern's diatomic series (or Stern-Brocot sequence): a(0) = 0, a(1) = 1; for n > 0: a(2*n) = a(n), a(2*n+1) = a(n) + a(n+1).

Gary W. Adamson's December 18, 2023 COMMENT (`%C`, verbatim):

> It appears that a(n) is equal to the multiplicative inverse of A007305(n+1) mod A007306(n+1).  For example, a(12) is 2, the multiplicative inverse of A007305(13) mod A007306(13), where A007305(13) is 4 and A007306(13) is 7.

The A002487 AUTHOR line (`%A`, verbatim):

> _N. J. A. Sloane_

OEIS A007305, NAME (`%N`, verbatim):

> Numerators of Farey (or Stern-Brocot) tree fractions.

OEIS A007306, NAME (`%N`, verbatim):

> Denominators of Farey tree fractions (i.e., the Stern-Brocot subtree in the range [0,1]).

The listing has 0/1 and 1/1 at indices 0 and 1. Each later level lists its
new mediants in increasing order in [0,1]. For
`r = 2^m + j`, `1 <= j <= 2^m`, entry `r` is
`fareyRow (m+1) (2*(j-1)+1)`. Equivalently, for `r >= 2`, take
`m = Nat.log 2 (r-1)` and `k = r-1-2^m`, then select row `m+1`,
position `2*k+1`. The first and second coordinates are `fareyNum` and
`fareyDen`.

The literal Lean statement is:

```lean
theorem result (n : ℕ) (hn : 0 < n) :
    stern n * fareyNum (n + 1) % fareyDen (n + 1) = 1 % fareyDen (n + 1)
```

Only Adamson's sentence is settled, for positive natural indices. The
Yurramendi frequency conjecture, Torres's conjectures and other Farey-tree
properties are not claimed.

## Motivation

The Stern scalar recurrence and the level-by-level mediant construction
define their objects independently. The inverse relation connects the
sequence value at one index to the fraction at the next index, uniformly
over every positive natural number.

## Gap

The supplied literature readings dated 2026-09-15 retain "It appears" in
the OEIS comment and contain no proof line. A007305 and A007306 do not
mention the relation. The arXiv API returned HTTP 503, so that surface was
not searched; OpenAlex returned four unrelated hits; the MathOverflow and
Math.SE APIs returned zero hits; non-mirror GitHub results and
formal-conjectures results were both zero. These readings do not establish
an exhaustive absence of prior proof.

Bates, Bunder and Tognetti (2010), "Linking the Calkin–Wilf and
Stern–Brocot trees", doi:10.1016/j.ejc.2010.04.002, concerns the
transposition relation between the two trees and does not state the
modular-inverse claim. Yurramendi's 2014 A002487 `%F` identity
`a(k+1)*a(2^m+k) - a(k)*a(2^m+(k+1)) = 1` is stated without proof.

Local prior-art search on `origin/dev` finds the frozen
`D5/S3/PrimeForms/SternBrocot/WordNodesAreReduced`, whose word-matrix
unimodularity statement is different, and an unrelated Farey-sequence gap
triage note. The pinned Mathlib search
`diatomic|Stern|Farey|CalkinWilf|mediant|Brocot` has four bibliographic
name hits and no Stern diatomic sequence or Farey-tree definition or
dominating theorem in that searched scope.

The supplied numerical readings are zero exceptions for
`1 <= n < 16384`, zero exceptions for `1 <= n < 4096`, and zero
column-constancy or determinant exceptions through level 12. They are
bounded fault-detection readings, not universal proofs.

Pre-registration #7993 is dated 2026-09-15T02:14:06Z, before the recorded
probe start at 02:14:58Z. Its proposed row-coordinate and determinant
invariants are the two private induction results used in the proof.

## Route

1. Prove the row-coordinate invariant
   `fareyRow m k = (stern k, stern (2^m+k))` for `k <= 2^m` by
   induction over all levels, separating copied even positions from newly
   inserted odd mediants.
2. Prove Yurramendi's determinant identity in its additive natural-number
   form
   `stern(k+1)*stern(2^m+k) = stern(k)*stern(2^m+k+1)+1` for
   `k < 2^m`, by level induction and the two parity cases.
3. For positive `n`, set `m = Nat.log 2 n` and `k = n-2^m`.
   The logarithm bounds give `n = 2^m+k` and `k < 2^m`. The
   row invariant identifies entry `n+1` with
   `(stern(2*k+1), stern(2*n+1))`.
4. The odd-index Stern recursion and the determinant express
   `stern n * fareyNum (n+1)` as a multiple of `fareyDen (n+1)`
   plus one. Taking natural remainders gives `result`.

## Falsifier

A positive natural `n` for which
`stern n * fareyNum (n+1) % fareyDen (n+1)` differs from
`1 % fareyDen (n+1)` would contradict the theorem. The statement
quantifies over every positive natural index, without a finite upper bound.

## Evidence

- Module: `D5/S3/PrimeForms/SternBrocot/AdamsonSternFareyInverse.lean`.
- Single-file `lake env lean`: exit 0.
- `tools/scripts/agent/header-check.sh` on the module: exit 0.
- The single-file profiler command with `-Dprofiler=true` and
  `-Dtrace.profiler.threshold=1000`: exit 0; wall time 5.216 seconds,
  type checking 309 milliseconds, warm cache and no concurrent Lean process.
- Scratch `#print axioms result`: Lean exit 0, exact closure
  `[propext, Classical.choice, Quot.sound]`.
- The elaborated `result` proof directly references both private theorems
  `row_coordinates` and `stern_determinant`; scratch inspection exits 0.
- Deleting either direct import, `Mathlib.Data.Nat.Log` or
  `Mathlib.Tactic.Linarith`, gives bare Lean exit 1. Both are necessary
  in the retained import set.
- The final Lean definitions evaluated at all 4097 indices
  `0 <= r <= 4096` agree with independent scalar-recursion and full-list
  mediant constructions; the comparison exits 0. All 4095 targets
  `1 <= n < 4096` have zero exceptions. Row coordinates, column
  identities, determinants and sorting have zero exceptions through level
  12. The example is `stern(12)=2`, entry 13 `(4,7)`.
- The numerical checks are finite experimental evidence; the universal
  claim is carried by the kernel-checked induction proofs.

## Triage

`theorem`. Adamson's modular-inverse relation is proved for every natural
`n` with `0 < n`; the resolution is `proved`.

## ASSUMED-UNVERIFIED

The supplied external quotations, literature-search readings, prior-paper
description, pre-registration timestamps and larger `n < 16384` scan have
not been independently reverified here because this task has no network
access. The arXiv surface remains unsearched after its reported HTTP 503.
No exhaustive literature, historical-openness or priority claim is made.
Scribe compilation, emitted-Markdown inspection, repository admission,
freezing and the required CI checks are outside the measured evidence above.
