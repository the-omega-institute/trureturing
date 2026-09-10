---
slug: oeis-a338636-continued-fraction-odd-square-mod-eight
bibkey: hanna2020a338636
doi: null
url: https://oeis.org/A338636
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Residue/ContinuedFractionOddSquare
---

# Divisibility of the A338636 coefficients by eight

## Problem

OEIS A338636 (Paul D. Hanna, Nov 04 2020) records the following NAME and
FORMULA lines, quoted verbatim from `Library/Recurrence/hanna2020a338636.md`:

NAME:
> G.f. A(x) satisfies: 1 = A(x) - x/(A(x) - 3^2*x/(A(x) - 5^2*x/(A(x) - 7^2*x/(A(x) - 9^2*x/(A(x) - ...))))), a continued fraction relation.

FORMULA:
> a(n) = 0 (mod 8) for n > 1 (conjecture).

Only this FORMULA conjecture is claimed proved. The entry's two further
conjectures are outside this resolution:

> For n > 0, a(n) = 1 (mod 3) iff n = A191107(k) for some k >= 1

> For n > 0, a(n) = 2 (mod 3) iff n = A186776(k) for some k >= 2 where A186776 is the Stanley sequence S(0,2)

## Motivation

This first-tier OEIS conjecture comes from Hanna's 2020 entry. The target is a
proof for all coefficient indices greater than one. KPI = open problems
resolved; no repository cumulative count is asserted.

## Gap

The supplied search-seat report found no proof in the OEIS entry or revision
history read on 2026-09-09, or in identifier searches on arXiv, MathOverflow,
and GitHub. This Stage-B seat had no network access and did not independently
repeat those searches. This bounded search does not establish publication priority.

## Route

`stabilization` is the escape content: finite-tail comparison gains one
coefficient of agreement per level, so each coefficient converges with depth
in the sense of eventual exact agreement. `hanna_conjecture` uses this result
through `generating_equation`, placing stabilization on the live proof path.

Only finite tails are modelled. For a terminal index D, write C_D = A and
C_j = A − (2j+1)²·x / C_(j+1) for j < D. In Lean,
`finiteTail A j d` denotes this tail with d levels and terminal index j+d;
`finiteTail A j` is the depth-indexed family. When A has constant coefficient
1, every denominator has constant coefficient 1 and is invertible. No infinite
continued-fraction object is assumed, and no claim is made that shifted
infinite tails coincide.

`a` reads coefficients from the depth-indexed approximation, and
`generatingSeries` assembles them. `generating_equation` faithfully states the
entry's relation 1 = A − x/C_1 as coefficient agreement through degree d+1
at every finite depth d, together with normalization and denominator unit
identities. `generating_unique` pins the normalized solution by the triangular
multiplier 1: determining the next coefficient requires no division by another
integer.

`hanna_conjecture` proves `8 ∣ a n` for `n > 1`. Modulo 8 every odd square
is 1, so the reduced relation collapses to the fixed point `1 + x`. Every
finite tail of that series agrees with 1 through its depth. Exact equality
of the entire finite tail with 1 would be false; the module asserts agreement,
not equality. Contraction uniqueness identifies the reduced generating series
with `1 + x`, whose coefficients above degree one vanish. The sole import is
`Mathlib.RingTheory.PowerSeries.Inverse`; target generality is G.

## Falsifier

A coefficient index n > 1 for the normalized series defined by the NAME
relation with `8 ∤ a n` would falsify the assertion. The orchestrator's exact
finite check is supporting evidence only, not a substitute for this universal
statement.

## Evidence

- Lean module: `D5/S1/Recurrence/Residue/ContinuedFractionOddSquare.lean`.
- Main theorem: `hanna_conjecture`.
- Companions: `finiteTail`, `stabilization`, `generating_equation`,
  `generating_unique`; coefficient definitions: `a`, `generatingSeries`.
- Axioms: std3 (`propext`, `Classical.choice`, `Quot.sound`) for all seven
  public declarations, confirmed by the Stage-B single-file Lean check (exit 0).
- Orchestrator-supplied readings attributed to `results/verify-r18.out`, as
  supporting evidence only: solving degree by degree from `a 0 = 1` gives
  integers reproducing the published DATA exactly:
  `1, 1, 8, 272, 19480, 2353568, 429016872`. The defining-relation residual is
  zero through degree 38. Divisibility by 8 holds at every index from 2 to 38,
  with zero violations. Independent solutions at depths 80 and 82 give
  identical coefficients, the measured form of stabilization. This seat did
  not independently inspect that output file.

## Triage

`theorem`. One resolution claim of kind `Proved` binds this dossier only to
`hanna_conjecture`, anchored on the quoted mod-eight FORMULA line.

## ASSUMED-UNVERIFIED

The source quotations were supplied by the orchestrator. The OEIS entry and
revision history were read by the search seat on 2026-09-09, not by this seat.
The reported literature scope was identifier search on arXiv, MathOverflow,
and GitHub, without an exhaustive search of all publications or private
indexes. This seat had no network access. The numerical readings above were
supplied by the orchestrator rather than reproduced here. Publication priority
and the identification of the source's informal continued fraction with the
formal finite-depth specification are not kernel-checked facts. Neither
mod-three conjecture is claimed resolved.
