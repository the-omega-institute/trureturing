---
slug: oeis-a204061-companion-pell-exp-base-five-residue
bibkey: hanna2012a204061
doi: null
url: https://oeis.org/A204061
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/CompanionPellExpBaseFiveResidue
---

# Hanna's A204061 coefficients modulo five

## Problem

OEIS A204061, NAME (`%N`, verbatim):

> G.f.: exp( Sum_{n>=1} A001333(n)^2 * x^n/n ) where A001333(n) = A002203(n)/2, one-half the companion Pell numbers.

COMMENT conjecture (`%C`, verbatim):

> a(n) == 1 (mod 5) iff n has no 2's in its base 5 expansion (A023729), otherwise a(n) == 0 (mod 5); this is a conjecture needing proof.

FORMULA (`%F`, verbatim):

> G.f.: 1 / ( sqrt(1+x) * (1-6*x+x^2)^(1/4) ).

AUTHOR (`%A`, verbatim):

```text
_Paul D. Hanna_, Jan 10 2012
```

The exact formal target is, for every `n : Nat`,
`exists z : Z_5, (z : Q_5) = a(n) and
PadicInt.toZMod z = (if 2 in Nat.digits 5 n then 0 else 1)`.
Here `a(n)` is coefficient `n` of the defining exponential in `Q_5`.
Its exponent uses the frozen sequence `Q : Nat → Nat` from
`D5/S1/Recurrence/PellCompanionGcd`: A001333, one-half the companion Pell
numbers, canonically embedded into `Q_5`. This proves the residue conjecture
in the 5-adic reading.

## Motivation

The conjecture links a recurrence-defined exponential to a base-five digit
condition at every natural index. Its unconditional residue law also
constructs a 5-adic integral representative for each coefficient.

## Gap

The orchestrator's readings dated 2026-09-15 report that the OEIS revision
still says "conjecture needing proof", with no settlement in `%C`, `%F`, or
`%H`. The supplied search results were: arXiv API `all:"A204061"`, zero
entries; OpenAlex `"A204061"`, zero; MathOverflow API, zero; GitHub code
search, only joeis/loda/OEIS-Spider mirrors and no Lean proof;
formal-conjectures, zero. The repository `prior-art.sh` search reported
zero `A204061` hits and only `PellCompanionGcd` for `A001333`. That module
supplies the frozen defining sequence and proves a gcd statement.
Pre-registration: issue #7889.

## Route

1. For the defining Pell-square exponential `f`, the order-three recurrence
   of the squared frozen sequence `Q` gives a differential equation. Formal
   differentiation proves constant coefficient one and
   `f^4 * ((1+X)^2 * (1-6X+X^2)) = 1`.
2. Let `R=(1+X)^2*(1-6X+X^2)`. Substitute `R-1` into the binomial series
   with exponent `-4.inv` over `Z_5` to construct `g` with `g^4*R=1` and
   constant coefficient one. Uniqueness of the fourth root with that
   constant coefficient in `Q_5` identifies its image with `f`.
3. Reduce `g` modulo five. Frobenius and the quartic equation give
   `B=(1+X+X^3+X^4)*B(X^5)` over `ZMod 5`, so coefficient `n` is zero when
   `n mod 5=2` and otherwise equals coefficient `n div 5`.
4. Inside `result`'s proof, a `have` performs strong induction through `n div 5`
   and identifies the coefficients with the indicator that the base-five
   expansion has no digit two. Apply this to the residue of coefficient `n` of `g`.

## Falsifier

A natural index whose exponential coefficient is not 5-adic integral, or
whose residue is neither the specified zero nor the specified one, would
contradict the theorem. At index zero the digit list is empty and the
coefficient is one. Finite tests alone cannot establish the universal law.

## Evidence

- `lake env lean D5/S1/Recurrence/Invariants/CompanionPellExpBaseFiveResidue.lean`:
  exit 0. The public declarations are exactly `a` and `result`.
- `#print axioms D5.S1.Recurrence.Invariants.CompanionPellExpBaseFiveResidue.result`:
  `[propext, Classical.choice, Quot.sound]`. The source contains no `sorry`.
- `tools/scripts/agent/header-check.sh D5/S1/Recurrence/Invariants/CompanionPellExpBaseFiveResidue.lean`:
  exit 0; seven-line header, generality `I`, `utility: none`.
- The orchestrator reports: measured by the orchestrator outside the sandbox:
  lean-report 0, emit 0 ×2, deposit-uncovered 0.

Single-import deletion checks, supplied to Lean by process substitution:

| Deleted import | Exit | Missing dependency |
| --- | --- | --- |
| `D5.S1.Recurrence.PellCompanionGcd` | 1 | Frozen sequence `Q` |
| `Mathlib.RingTheory.PowerSeries.Exp` | 1 | `PowerSeries.exp` |
| `Mathlib.RingTheory.PowerSeries.Binomial` | 1 | `binomialSeries` |
| `Mathlib.RingTheory.PowerSeries.Expand` | 1 | `MvPowerSeries.map_frobenius_expand` |
| `Mathlib.NumberTheory.Padics.MahlerBasis` | 1 | 5-adic types and their binomial structure |
| `Mathlib.FieldTheory.Finite.Basic` | 1 | `ZMod.frobenius_zmod` |

## Triage

`theorem`, resolution `proved` for the exact kernel-checked 5-adic statement
above.

## ASSUMED-UNVERIFIED

Exhaustive literature coverage, priority, and integrality over `ℤ` are not
established by this result.
