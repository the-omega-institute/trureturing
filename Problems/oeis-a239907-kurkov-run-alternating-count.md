---
slug: oeis-a239907-kurkov-run-alternating-count
bibkey: sloane2014a239907
doi: null
url: https://oeis.org/A239907
triage: theorem
motivation_gids:
  - D5/S1/Digit/KurkovRunAlternatingCount
---

# Kurkov's alternating binary run count

## Problem

OEIS A239907, NAME (`%N`, verbatim):

> Let cn(n,k) denote the number of times 11..1 (k 1's) appears in the binary representation of n; a(n) = n - cn(n,1) + cn(n,2) - cn(n,3) + cn(n,4) - ... .

The settled FORMULA (`%F`, verbatim):

> Conjecture: a(n) = n - A329320(n) for n >= 0 (noticed by Sequence Machine). - _Mikhail Kurkov_, Oct 13 2021

AUTHOR (`%A`, verbatim):

> _N. J. A. Sloane_, Apr 07 2014

Occurrences overlap. In the binary word `111`, the counts for block lengths
1, 2, and 3 are 3, 2, and 1; hence `a(7)=7-3+2-1=5`, as required by the
data. Numbering bits from the least significant end preserves counts of
the palindromic block of ones. The index range has length `n.size`, the
binary length, with the empty range at zero.

For every natural `n`, define `cn(n,k)` to count starts `i<n.size` with
`n.testBit(i+j)=true` for every `j<k`. Define `b(n)` to count starts
`i<n.size` for which `v_2(n div 2^i+1)` is odd, where `div` is natural
floor division. For positive `n` this is the A329320 NAME sum under the
supplied characterization `1-A035263(m)=[v_2(m) odd]` for positive `m`.
All valuation arguments are positive. At `n=0` both ranges are empty,
so the identity reads `0=0`.

The exact Lean statement, with integer subtraction and integer summands, is:

```lean
theorem result (n : ℕ) :
    (n : ℤ) - ∑ k ∈ Finset.Icc 1 n.size, (-1 : ℤ) ^ (k + 1) * (cn n k : ℤ) =
      (n : ℤ) - (b n : ℤ)
```

Only Kurkov's quoted `%F` line is settled. The interpretation of A329320
uses the cited valuation characterization; the morphism-to-valuation
identity for A035263 is not independently formalized here.

## Motivation

The left side counts overlapping blocks across all lengths with alternating
signs. The right side counts binary suffixes by valuation parity. Their
identity gives a uniform description at every natural index and explains
the cancellation within each suffix's trailing run of ones.

## Gap

Readings of 2026-09-15: OEIS still marks the line
`Conjecture` and A329320 carries `[verification needed]`. OpenAlex returned
0 hits for `A239907`, the Math.SE API returned 0, and formal-conjectures
returned 0. The arXiv API returned HTTP 429/503, so arXiv was not searched.
The repository prior-art search at `origin/dev = af6885715e`
found no declaration of an overlapping block count, of A329320, or of the
period-doubling sequence in D5, Library, or Problems; the frozen
`D5/S1/Digit/YanevRunCompressionClosedForm` defines binary runs for a
different (run-compression) statement that neither dominates nor is used
by this identity. Pinned Mathlib supplies `Nat.testBit`, `Nat.size`, `padicValNat`,
and `neg_one_geom_sum`, but no substring-count definition was found in
the searched scope. The dominating-theorem search outcome is
`not-found-in-searched-scope`; this is not an exhaustive absence claim.

Numerical checks found zero exceptions for `0 <= n < 65536` and, against
the final definitions, for `0 <= n < 4096`. These finite checks detect
faults and do not prove the unbounded identity.

Pre-registration issue #8060 was created on 2026-09-15 before the probe
started, according to the supplied registration reading. The question
answered is exactly the quoted identity for every natural `n`, on the
first-tier small external OEIS-conjecture route. Registration timing and
historical openness have not been independently checked here.

## Route

1. For a natural `m`, all of its lowest `k` bits are one exactly when
   `2^k` divides `m+1`. The bit-mask identities and
   `padicValNat_dvd_iff_le` turn this into `k <= v_2(m+1)`.
2. At start `i<n.size`, use `m=n div 2^i`. The run length is
   `v_2(n div 2^i+1)` and is at most `n.size`: any longer run would
   require a nonzero bit beyond the binary length. Counts for lengths
   beyond `n.size` therefore vanish.
3. Interchange the finite sum over lengths with the finite sum over
   starts. For run length `r`, `neg_one_geom_sum` gives
   `sum_{k=1..r} (-1)^(k+1) = [r odd]`. Summing these indicators gives
   `b(n)`, and subtraction from the integer `n` yields the identity.

The theorem has `proof_shape: bind-only`, `escape_witness: null`, and
`admission_basis: open-problem-resolution` under the supplied
pre-registration #8060. Its steps are upstream instantiation, finite-sum
reordering, and normalization. All supporting facts are local `have`
terms inside `result`; the public surface is exactly `cn`, `b`, and
`result`, with no helper declarations and no direct frozen-project
dependencies. The Scribe theorem carries the `Proved` resolution claim.

`utility: none` applies to every declaration. The definitions and the
all-natural symbolic identity are not bounded enumeration, checker
infrastructure, numeric reduction, or certified finite instances. No
numerical experiment supplies a formal premise; computational instance,
consumer, and premise fields are `not-applicable(kind=none)`.

## Falsifier

A natural `n` for which the alternating overlapping substring count
differs from `b(n)` would refute the displayed identity. A discrepancy
between the cited A035263/A329320 interpretation and the valuation
definition would instead refute the source interpretation. These are
separate falsifiers; only the first is excluded by the kernel theorem.

## Evidence

- `lake env lean -Dprofiler=true -Dtrace.profiler=true
  -Dtrace.profiler.threshold=1000 D5/S1/Digit/KurkovRunAlternatingCount.lean`:
  exit 0. `/usr/bin/time -p` reports wall 1.64 seconds; Lean reports
  type checking 21.5 milliseconds and import 689 milliseconds. This is
  a single-file, warm-cache measurement with Lean 4.33.0 on arm64 macOS.
- `lake env lean /private/tmp/impl-a239907/Axioms.lean`: exit 0. This
  scratch file contains the final module source followed by axiom queries.
  Each of `cn`, `b`, and `result` has exactly
  `[propext, Classical.choice, Quot.sound]`. The specialization
  `result 0` and the domain inhabitant `(0 : ℕ)` also type-check.
- `tools/scripts/agent/header-check.sh D5/S1/Digit/KurkovRunAlternatingCount.lean`:
  exit 0; 115 lines, 42 Lean files in the immediate directory, and
  `generality: G` compliant.
- Deleting either final direct import through process substitution and
  running `lake env lean`: exit 1 for `Mathlib.Data.Nat.Size`, with
  unknown `Nat.lt_size_self`; exit 1 for
  `Mathlib.NumberTheory.Padics.PadicVal.Basic`, with missing `Finset`
  and associated notation. The retained imports supply the bit,
  valuation, geometric-sum, and normalization APIs transitively.
- `python3 /private/tmp/impl-a239907/numeric.py`: exit 0. The final `cn`
  and `b` definitions were matched byte-for-byte to the probe before
  rerunning its Python check. For `0 <= n < 4096` there are zero identity
  exceptions, zero independent binary-string overlapping-count mismatches,
  zero tail mismatches, and zero bit/valuation bridge mismatches.
  `cn(7,2)=2`, and the first 16 terms agree with the supplied data.
  This is a Python model of the exact definitions, not native execution
  of the noncomputable Lean definition `b`.

## Triage

`theorem`; resolution `proved` for Kurkov's quoted formula under the
explicit valuation interpretation and scope wall above.

## ASSUMED-UNVERIFIED

The arXiv search was not performed (HTTP 429/503 at query time).
Historical openness outside the checked surfaces (OEIS text, OpenAlex,
Math.SE, formal-conjectures, repository prior art) is unverified, and no
exhaustive literature search or priority claim is made. A035263's morphic
definition is not formalized; the module uses its 2-adic valuation
characterization as the definition of `b`. Bounded numerical checks do not
establish the universal identity.
