---
slug: bala-a258899-totient-period
bibkey: bala2025a258899a258903
doi: null
url: https://oeis.org/A258899
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Periodic/BalaDivisorFactorialTotientPeriod.result
---

# Bala's A258899 and A258903 totient-period conjectures

## Problem

Peter Bala's COMMENTS conjecture for OEIS A258899 and A258903 states:

> Conjecture: the sequence a(n) taken modulo a positive integer k is eventually periodic with the period dividing phi(k).

The two sequences use the FORMULA fields

$$a_{899}(n)=\sum_{d\mid n}2^d\,\frac{n!}{d!(n/d)!},\qquad
a_{903}(n)=\sum_{d\mid n}2^d3^{n/d}\,\frac{n!}{d!(n/d)!}$$

for $n\ge1$, with value $1$ at index zero. The settling declaration states the two eventual-period assertions literally, with natural-number division and `Nat.ModEq`.

### Statement echo

For each positive natural modulus $m$, the result supplies an onset $N$, a positive natural period $T$ dividing `Nat.totient m`, and the congruence for every $n\ge N$, separately for A258899 and A258903.

## Motivation

The source entries are OEIS A258899 and A258903, revisions recorded in the literature note `D5/L/RecurrenceComposition/bala2025a258899a258903`. The problem was preregistered in [issue #24054](https://github.com/the-omega-institute/trureturing/issues/24054) before the formal proof.

## Gap

The source marked both eventual-period assertions as conjectures. The bounded literature screen recorded in #24054 found no inspected source settling either target. Literature completeness is `ASSUMED-UNVERIFIED`.

## Route

For $n\ge 2m+4$, a proper factorization $n=d e$ with $d,e\ge2$ gives $d+e+m\le n$. Factorial divisibility then makes $m$ divide the factorial quotient, so only $d=1$ and $d=n$ survive modulo $m$. For arbitrary natural weights $u,v$, the surviving terms are $u v^n+v u^n$. The imported theorem `D5.S1.Recurrence.Periodic.StirlingTransformTotientPeriod.pow_add_totient` makes both powers unchanged after a shift by $\operatorname{totient}(m)$. The weights $(2,1)$ and $(2,3)$ give the two source sequences, with $N=2m+4$ and $T=\operatorname{totient}(m)$.

## Falsifier

A modulus and tail index satisfying the hypotheses but violating either displayed `Nat.ModEq` conclusion would refute the settlement. A smaller uniform onset or period may sharpen the result but does not refute it.

## Evidence

The kernel-checked settling declaration is `D5/S1/Recurrence/Periodic/BalaDivisorFactorialTotientPeriod.result`; its module state is `Golden/Frozen/state/D5/S1/Recurrence/Periodic/BalaDivisorFactorialTotientPeriod.lean.json`. The scoped Lean report records the public declaration axiom closure inside {propext, Classical.choice, Quot.sound}.

Independent finite checks are published in the experiments repository at commit [`96efa433d49769b9ab2f8e0fb1263b9ca0725b6e`](https://github.com/the-omega-institute/trureturing-experiments/tree/96efa433d49769b9ab2f8e0fb1263b9ca0725b6e/docs/reports/bala-a258899-a258903), path `docs/reports/bala-a258899-a258903/check.py`. The script SHA-256 is `12c906c780a8b964892bf4dfe987eb5254ed0c2e089260d72b6999a1309a016a`. The command `python3 docs/reports/bala-a258899-a258903/check.py` exits 0 with `ALL_CHECKS_OK`; it checks the finite ranges reported by the source program and is not the universal proof.

Four-slot escape auditing is unfinished for `D5/S1/Recurrence/Periodic/BalaDivisorFactorialTotientPeriod.result`; issue [#25641](https://github.com/the-omega-institute/trureturing/issues/25641) records the missing lawful registration evidence. No `declared_validated` or `DTR-Declared` status is claimed before the required CI reading.

## Triage

The settlement is **Proved** by `D5/S1/Recurrence/Periodic/BalaDivisorFactorialTotientPeriod.result`. Its proof shape is bind-only after helper expansion; the admission basis is `open-problem-resolution (#24054; Proved)`.

| item | status | evidence |
| --- | --- | --- |
| Mechanism: proper-factor terms vanish for $n\ge2m+4$, leaving the two explicit exponential tails | proved | Kernel-checked `...result`, using the consumed factorial-divisibility and divisor-tail helpers. |
| Extension and surviving neighbours: the tail formula and totient shift hold for every natural pair $(u,v)$, including zero | proved | The same kernel-checked result's consumed general-weight tail and period steps. |
| Common witnesses: both source sequences use $N=2m+4$ and $T=\operatorname{totient}(m)$, including $m=1$ | proved | Kernel-checked `...result` supplies those witnesses and `Nat.totient_pos`. |
| Independent finite checks: 43,350 proper terms, 168,960 generic tails, 151,328 totient shifts, and 242,088 power periods on the script's finite ranges | computed | `python3 docs/reports/bala-a258899-a258903/check.py`, exit 0, script SHA-256 above; finite checks are not the universal proof. |
| Sharp bounds: least onset or least eventual period for each modulus and weight pair | open | No declaration in this delivery addresses minimality. |
| Literature completeness | open | `ASSUMED-UNVERIFIED`; the inspected source set does not establish exhaustive coverage. |

### What the settlement shows

The decisive mechanism is factorial divisibility for proper factors after the explicit onset, followed by the existing totient power-period theorem. The argument extends to arbitrary natural weights, removes any positivity requirement on the weights, includes modulus one, and supplies common witnesses for both OEIS sequences. The least possible onset and least eventual period remain open.

## ASSUMED-UNVERIFIED

Literature completeness is `ASSUMED-UNVERIFIED`; unsearched full texts and rate-limited indices remain outside the inspected scope. Escape registration remains unfinished under issue #25641 until a lawful typed registration and its required CI DTR reading exist.
