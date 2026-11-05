---
slug: arxiv-2506-09912-shkolnikov-sandpile-limit-divisible
bibkey: shkolnikov2025sandpilelimits
doi: 10.48550/arXiv.2506.09912
url: https://arxiv.org/abs/2506.09912v3
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/Sandpiles/ShkolnikovSandpileLimitDivisible.result
---

## Problem

Mikhail Shkolnikov, *Algebraic Limits of Sandpiles*, arXiv:2506.09912v3, Section 3, states that the image of the direct limit of rectangular sandpile groups may be a rational subtorus or a divisible group. The settled question is the divisibility alternative: for every positive rectangle, every circle-valued sandpile function on it, and every positive integer $k$, a later rectangular stage contains a sandpile function whose $k$-fold sum equals the signed reflected image of the original function.

### Statement echo

The Lean declaration `D5.S3.StatisticalMechanics.Sandpiles.ShkolnikovSandpileLimitDivisible.claim` preserves the six binding conventions from issue #20011: the carrier is `AddCircle (1 : ℝ)`; `InRect` is the open integer rectangle; `IsSandpile` is zero extension plus the four-neighbour equation; `unfold` is the parity-reflected coordinate; `embed` is the signed reflected zero extension; and the quantifiers require positive $p,q,k$, a sandpile $f$, and a later $g$ with the exact equality. The theorem `result` proves this proposition without weakening its quantifiers.

## Motivation

Divisibility supplies a structural property of the direct limit that is stronger than the previously known existence of elements of every finite order. The source's dual torsion question and the full image description are related but require additional identifications.

## Gap

The source left divisibility as an expectation. The literature screen recorded in issue #20011 found the expectation still open and found no repository declaration settling the same claim. Literature completeness is `ASSUMED-UNVERIFIED`.

## Route

The proof uses reversible row dynamics. A finite-denominator lift of the first row lies in a finite subgroup, so the injective transfer orbit is periodic. Reflection at a zero boundary row gives a closing period and the signed reflected tile formula. The resulting rows define the later sandpile, and recurrence uniqueness gives the required $k$-fold equality. The construction uses $m=1$ and only increases the vertical parameter.

## Falsifier

A counterexample would be a positive rectangle, sandpile $f$, and $k\ge1$ for which no positive later height and no sandpile $g$ satisfy the exact equality in `claim`. A proof failure would also invalidate the settlement if any recurrence, boundary, finite-period, or embedding equality used by `result` were false.

## Evidence

The kernel-checked declaration is `D5.S3.StatisticalMechanics.Sandpiles.ShkolnikovSandpileLimitDivisible.result`. Its axiom closure is contained in `{propext, Classical.choice, Quot.sound}`. The module state is `Golden/Frozen/state/D5/S3/StatisticalMechanics/Sandpiles/ShkolnikovSandpileLimitDivisible.lean.json`.

The independent exact-arithmetic experiment is pinned to [the experiment repository](https://github.com/the-omega-institute/trureturing-experiments/tree/bbde430b0cc8eda810ff64dd2fe3bc1ac77c2e0c/docs/reports/shkolnikov-2025-sandpile-limit-divisibility). The command `python3 docs/reports/shkolnikov-2025-sandpile-limit-divisibility/check.py` exits 0; the script SHA-256 is `8b5716cb00667a95f59381cda86b8ab69d97445eca6cc13418bf6b4406b29617`. It checks 45 harmonic-root and embedding cases for $(p,q)\in\{(2,2),(3,2),(2,3),(3,3),(4,3)\}$, $k\in\{2,3,5\}$, and three sampled elements per pair, together with the six source Table 1 group orders.

## Triage

| item | status | evidence |
| --- | --- | --- |
| Exact preregistered divisibility claim | proved | Kernel-checked `result`; the claim is the full proposition above. |
| Reversible finite-denominator row dynamics, zero-row reflection, and a closing period | proved | The live proof path of `result` uses `rows_reflect`, `rows_double_period`, `rows_tile`, and `finite_row_lift`. |
| Only vertical enlargement is required | proved | `result` constructs witnesses with $m=1$ and a positive vertical multiplier. |
| Complete image in the inverse limit of extended groups | open | No declaration in this delivery identifies the image. |
| Rational-subtorus alternative | open | No declaration in this delivery proves the alternative. |
| Pontryagin-dual/inverse-limit identification and the torsion-free corollary | open | The dual translation is not formalized by `result`. |
| Explicit numerical upper bound on the chosen period | open | `finite_row_lift` proves existence of a period but gives no numerical bound. |
| Review the standalone proof and source fidelity | proved | The delivered Lean definitions, Scribe formulas, and source note preserve the preregistered conventions. |

### Declaration judgement

| declaration | proof_shape | escape_witness | consumers |
| --- | --- | --- | --- |
| `D5.S3.StatisticalMechanics.Sandpiles.ShkolnikovSandpileLimitDivisible.result` | bind-only | none; the external named open-problem resolution is the admission basis | none |

The module admission basis is `open-problem-resolution (#20011; Proved)`. The public result is the designated settling theorem and is not a four-slot registration claim. Its typed Reg mirror compiles, but the lawful enrolled readout and source-coordinate evidence remain unfinished under [issue #20360](https://github.com/the-omega-institute/trureturing/issues/20360).

## ASSUMED-UNVERIFIED

The literature search establishes the source's stated expectation and the searched-scope absence of a settlement; it does not establish exhaustive worldwide completeness. The publisher text cited by the preregistration was not independently inspected beyond the arXiv source. The Reg mirror has no `declared_validated` DTR reading at the delivered head, so the escape audit remains unfinished under issue #20360.
