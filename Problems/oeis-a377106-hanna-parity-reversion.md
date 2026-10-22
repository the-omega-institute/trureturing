---
slug: oeis-a377106-hanna-parity-reversion
bibkey: hanna2024a377106
doi: null
url: https://oeis.org/A377106
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/HannaA377106ParityReversion
---

# Integrality and dyadic parity of OEIS A377106

## Problem

> Conjecture: a(n) is odd iff n = 2^k for some k >= 0.

The entry defines $A^3=A(x^3+9xA^3)$, $A(0)=0$, $[x]A=1$. A normalized rational solution exists, and every such solution has integer coefficients at each $n\geq1$, with odd coefficient exactly when $n=2^k$ for some natural $k$.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| the displayed cubic equation and normalization | IsGF contains all three source conditions over rational power series | exact registered convention |
| offset one | claim quantifies over every n at least one | exact registered convention |
| odd iff a power of two | claim supplies an integer coefficient and its Odd equivalence | exact registered convention |
| the entry describes a series | claim also asserts existence; uniqueness transfers the conclusion to every normalized solution | exact registered convention |

## Motivation

The externally stated OEIS conjecture is preregistered in #18788. The settling declaration is `D5.S1.Recurrence.Invariants.HannaA377106ParityReversion.result`; its admission basis is `open-problem-resolution (#18788; Proved)`.

## Gap

The preregistration records the OEIS source and literature screen. The checked entries cite no proof. Literature-screen completeness is ASSUMED-UNVERIFIED. The mathematical gap is discharged by the settling declaration under the displayed coefficient rings and normalizations.

## Route

`HannaPrimeSubstitutionIntegrality.General.exists_integral` at $p=3,c=9$ constructs an integer solution. `HannaPrimeSubstitutionIntegrality.General.solution_unique` transfers it to every rational solution. Reduction modulo two and `CubicFifteenSubstitutionParity.thue_series_equation` identify its reduction with `CubicFifteenSubstitutionParity.powerTwoSeries`.

## Falsifier

A normalized rational solution with a noninteger positive-index coefficient or a parity exception would contradict `result`.

## Evidence

The Lean module and its Blueprint Scribe carry the exact statement. The axiom closure is contained in {propext, Classical.choice, Quot.sound}. The frozen module record is `Golden/Frozen/state/D5/S1/Recurrence/Invariants/HannaA377106ParityReversion.lean.json`. Escape audit unfinished: [#19794](https://github.com/the-omega-institute/trureturing/issues/19794); no compiled registration is delivered.

### Experiment

[Pinned experiment](https://github.com/the-omega-institute/trureturing-experiments/tree/51e113e1cec22e8545ea90ca42a5fe6da21d4c88/docs/reports/oeis-a377106-hanna-parity-reversion). Command: `python3 check.py` in that directory; exit 0; script SHA-256 `cb5f55362dd90921fd2a5eae58f05cc718583a0dcfbe00ec8e7b7fd30276aafe`.

Computed through order 150: every division by three is exact, the reversed series reduces to $y+y^2$ modulo two, the first 12 terms match the entry, and the functional equation holds. Odd indices through 150 are exactly $1,2,4,8,16,32,64,128$.

### Declaration classification

Same-delivery helpers are expanded for classification; consumed bind-only helpers are proof organization. The table names live consumers and the surviving construction or induction witness.

| Declaration | proof_shape | escape_witness | Consumers |
| --- | --- | --- | --- |
| `D5.S1.Recurrence.Invariants.HannaA377106ParityReversion.IsGF` | bind-only | `none` | `D5.S1.Recurrence.Invariants.HannaA377106ParityReversion.claim`, `D5.S1.Recurrence.Invariants.HannaA377106ParityReversion.result` |
| `D5.S1.Recurrence.Invariants.HannaA377106ParityReversion.claim` | bind-only | `none` | `D5.S1.Recurrence.Invariants.HannaA377106ParityReversion.result` |
| `D5.S1.Recurrence.Invariants.HannaA377106ParityReversion.map_solution` | bind-only | `none` | `D5.S1.Recurrence.Invariants.HannaA377106ParityReversion.result` |
| `D5.S1.Recurrence.Invariants.HannaA377106ParityReversion.result` | content | `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.solution_unique` |  |

## Triage

| Item | Status | Evidence kind |
| --- | --- | --- |
| Normalized solution existence, coefficient integrality, and dyadic parity (#18788) | proved | kernel-checked `result` |
| The shared prime construction (#18792) | proved | kernel-checked `HannaPrimeSubstitutionIntegrality.result` |
| Somos prime classification (#18793) | proved | kernel-checked `SomosPrimeIntegrality.result` |
| Coefficient and parity comparison through order 150 | computed | pinned experiment; exact scope above |
| General c congruent to 1 modulo 2 and 0 modulo 3 | proved in prose | the general-c argument below; no separate kernel-checked declaration |
| Other Hanna odd-iff-power-of-two entries | open | outside this claim |
| Mathematical remaining goals for the three registered settlements | proved | the three result declarations discharge the registered claims |

### What the settlement shows

Proved in Lean: every normalized rational solution, rather than a chosen solution, has the claimed integrality and parity at every positive index. The decisive mechanism is reduction modulo two combined with normalized uniqueness. The entry's integrality and parity assertions are settled. For the neighbouring family, let $c$ be an odd integer divisible by three. The shared integral construction at $p=3$ gives a normalized integral $G$ satisfying $G^3=G(x^3+cxG^3)$. Its reduction modulo two has coefficient $c=1$, so it obeys the same equation as the dyadic-support series $T=\sum_{k\geq0}x^{2^k}$. The identity for $T$ is `CubicFifteenSubstitutionParity.thue_series_equation`: its coefficient 15 also reduces to one. Normalized uniqueness over the field of two elements (where 3 is nonzero) forces $G\bmod2=T$. Over the rationals normalized uniqueness transfers integrality and parity to every solution. This proves the odd-$c$, three-divisible family in prose from the same general construction and uniqueness; it is not a separate Lean assertion. The other listed Hanna entries are outside this claim.

## ASSUMED-UNVERIFIED

Literature completeness and originality are not established. The other source families and uniform extensions marked open above are outside this settlement. Four-slot escape registration remains unfinished under #19794.
