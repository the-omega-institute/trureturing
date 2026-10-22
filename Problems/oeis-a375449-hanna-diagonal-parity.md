---
slug: oeis-a375449-hanna-diagonal-parity
bibkey: hanna2024a375449a375452
doi: null
url: https://oeis.org/A375449
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/HannaDiagonalDerivativeParity.result
---

# Hanna's OEIS A375449 diagonal derivative parity conjecture

## Problem

P. D. Hanna's OEIS A375449 asks about the normalized rational power series whose coefficients satisfy

> Expansion of g.f. A(x) satisfying [x^n] x*A'(x) / (1 - n*A(x)) = n^(n+1) for n >= 1.

Its Comments field states:

> Conjecture: for n > 1, a(n) is odd iff n is of the form 2^k-2 or 2^k-1 for some k > 1.

The formal statement uses zero constant coefficient and the literal formal derivative and unit-denominator inverse. It asserts existence of a rational solution and integral coefficients with the stated parity support.

### Statement echo

| source clause | Lean counterpart | fidelity |
| --- | --- | --- |
| $[x^n]xA'(x)/(1-nA(x))=n^{n+1}$ for $n\ge1$ | `D5.S1.Recurrence.Invariants.HannaDiagonalDerivativeParity.IsGF` | The formal derivative, coefficient operator, rational scalar, and inverse are literal. |
| offset one and normalized solution | `constantCoeff A = 0` in `IsGF` | The constant coefficient condition is explicit. |
| odd exactly at $2^k-2$ or $2^k-1$ for $n>1$ | `claim` and `result` | The quantifiers and natural subtraction are literal. |

## Motivation

The settlement answers the explicitly stated A375449 conjecture and supplies the shared diagonal parity theorem used by the sibling A375452 settlement.

## Gap

The source entry leaves the parity classification as a conjecture. The source and repository literature screen are bounded; completeness is `ASSUMED-UNVERIFIED`.

## Route

`diagonal_integral_parity` proves the integral solution and its universal parity classification whenever an integer forcing sequence reduces to $n$ modulo two. Its proof uses the strict coefficient contraction, the reduction to the Mersenne series, and the disjoint odd and even supports of the series and its square. `result` instantiates the forcing sequence with $t(n)=n^n$ and identifies the source equation with `IsDiagonal`.

## Falsifier

A rational normalized solution with a coefficient at some $n>1$ whose parity differs from the two stated support families, or a failure of the source equation to match `IsGF`, would contradict `result`. Finite agreement alone would not settle the universal claim.

## Evidence

The kernel-checked declarations are `D5.S1.Recurrence.Invariants.HannaDiagonalDerivativeParity.IsGF`, `D5.S1.Recurrence.Invariants.HannaDiagonalDerivativeParity.claim`, `D5.S1.Recurrence.Invariants.HannaDiagonalDerivativeParity.diagonal_integral_parity`, and `D5.S1.Recurrence.Invariants.HannaDiagonalDerivativeParity.result`. Their axiom closure is contained in `{propext, Classical.choice, Quot.sound}`.

The independent finite check is published at [oeis-hanna-parity-family-research](https://github.com/the-omega-institute/trureturing-experiments/tree/9dfe5bdc210cac281a148e7180239ddb21b0b34b/docs/reports/oeis-hanna-parity-family-research). Command: `python3 docs/reports/oeis-hanna-parity-family-research/check.py`; exit 0. Script SHA-256: `ec87bb1637d6a946d4e5fb43f078bc623ce327257ef53b9305c05c564ca154b5`. It checks both sequences against OEIS data and the parity rule for $2\le n\le60$.

## Triage

### What the settlement shows

- **Proved in Lean:** A375449's normalized equation has an integral solution and its coefficients are odd exactly on $2^k-2$ and $2^k-1$ for $n>1$, by `result`.
- **Proved in Lean:** The arbitrary integer forcing theorem under the residue condition has two consumers, `result` in this module and the sibling A375452 result, by `diagonal_integral_parity`.
- **Computed:** The experiment checks both forcing sequences through $n=60$; it does not establish a uniform extension beyond that range.
- **Open:** Sharper coefficient formulas and classifications outside the two support families remain outside this settlement.

## ASSUMED-UNVERIFIED

The literature screen does not establish exhaustive worldwide completeness or publication priority beyond the searched scope recorded for the preregistration.
