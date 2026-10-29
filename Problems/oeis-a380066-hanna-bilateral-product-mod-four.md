---
slug: oeis-a380066-hanna-bilateral-product-mod-four
bibkey: hanna2025a380066
doi: null
url: https://oeis.org/A380066
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Bilateral/BilateralProductModFourUnitExponent.result
---

# Hanna's A380066 bilateral product congruence

## Problem

Paul D. Hanna's [OEIS A380066](https://oeis.org/A380066) states:

> G.f. A(x) satisfies 1/2 = Sum_{n=-oo..+oo} x^n*A(x)^n * (A(x)^n + x)^(n-1) * (A(x) + x^n)^(n-1).

> Conjecture: for n > 0, a(n) == 2 (mod 4).

The offset is zero and the listed coefficients begin $1,6,62,826,13562$. The binding convention in [#18805](https://github.com/the-omega-institute/trureturing/issues/18805) uses integer power series with $A(0)=1$. Each coefficient $N$ is read through every symmetric integer window $[-K,K]$ with $N\le K$ in rational Laurent series. This is a formal coefficient statement, with no analytic convergence claim.

### Statement echo

All new names belong to `D5.S1.Recurrence.Bilateral.BilateralProductModFourUnitExponent`.

| Source clause or binding convention | Lean counterpart | Fidelity |
| --- | --- | --- |
| The displayed summand, with every integer index | Frozen `BilateralProductModFour.laurentTerm` at parameter one | The source expression is reused literally. |
| Offset zero and constant coefficient one | `HannaA380066.IsGF`, first conjunct | The integer-series convention and normalization are explicit. |
| The bilateral equation | `HannaA380066.IsGF`, every `N`, `K` and window hypothesis | Every coefficient and every radius at least its index are required. |
| Every positive index has residue two modulo four | `HannaA380066.claim`, universal conjunct; `result` | Every normalized integral solution is covered. |
| Existence | `HannaA380066.claim`, existential conjunct; `result` | This rules out a vacuous universal assertion and adds no hypothesis. |

The two public definitions retain the literal binding conventions. The proof uses the existing family's owners internally. There are no additional source assumptions.

## Motivation

The source is an explicitly stated, externally published conjecture (tier 1). The settling GID is `D5/S1/Recurrence/Bilateral/BilateralProductModFourUnitExponent.result`, with admission basis `open-problem-resolution (#18805; Proved)`. It is frozen by `deposit-uncovered`, without an atom or coverage step. Its Scribe contains one `OpenProblemResolutionClaim`, with resolution `Proved`.

## Gap

The frozen `BilateralProductModFour` family supplies the summands and series construction, but its generating-equation, uniqueness and congruence theorems assume $2\le c$. Those hypotheses do not cover $c=1$.

The literature screen recorded in #18805 reads the OEIS entry. The search producer reports checking classical bilateral summations (DLMF sections 17.8 and 20.5), Schlosser's arXiv:math/0302270 and Kallat's arXiv:2610.15849; those readings are producer-reported. Strehl, Discrete Mathematics 99 (1992), is not read. The screen found no proof of this conjecture in its stated scope; completeness is `ASSUMED-UNVERIFIED`.

## Route

For each $c\ge1$, write the nonzero-index remainder as $H=S_c(A)$. Positive summands have order at least their positive index; the negative summand at $-m$ has order at least $cm^2\ge m$. The private `term_order`, `outside_zero` and `finite_window` give coefficientwise finite windows. The consumed private contraction lemmas show that the fixed-point step improves agreement by one degree. The induction in `UnitExponent.approximation_stable` stabilizes the existing approximations; `generating_fixed` and `generating_equation` establish the normalized integral solution. The private `polynomial_unique` and `generating_unique` identify every normalized integral solution with it.

At the fixed point, $(1+x)(1+A)(1-2H)=2$. The private `coefficient_four_dvd` establishes divisibility by four of the difference from $2/(1+x)-1$, coefficientwise. `hanna_conjecture_general` yields residue two at every positive index for all $c\ge1$; `result` specializes to the source's parameter one and transports the conclusion to every normalized integral solution.

### Declaration classification

The table expands the same-delivery helper graph to frozen and pinned-upstream boundaries. Names are relative to the module namespace; the consumers are extracted from elaborated proof terms.

| declaration | proof_shape | escape_witness | direct consumers |
| --- | --- | --- | --- |
| UnitExponent.term_order | bind-only | none | UnitExponent.outside_zero |
| UnitExponent.outside_zero | bind-only | none | UnitExponent.finite_window |
| UnitExponent.finite_window | bind-only | none | UnitExponent.laurent_window, UnitExponent.sum_zero |
| UnitExponent.sum_zero | bind-only | none | UnitExponent.step_agree, UnitExponent.step_zero |
| UnitExponent.term_agree | bind-only | none | UnitExponent.sum_agree |
| UnitExponent.sum_agree | bind-only | none | UnitExponent.step_agree |
| UnitExponent.step_zero | bind-only | none | UnitExponent.polynomial_form |
| UnitExponent.step_agree | bind-only | none | UnitExponent.approximation_stable, UnitExponent.generating_fixed, UnitExponent.polynomial_unique |
| UnitExponent.approximation_stable | content | UnitExponent.approximation_stable | UnitExponent.generating_agree |
| UnitExponent.generating_agree | content | UnitExponent.approximation_stable | UnitExponent.generating_fixed |
| UnitExponent.generating_fixed | content | UnitExponent.approximation_stable | UnitExponent.coefficient_four_dvd, UnitExponent.polynomial_form, UnitExponent.polynomial_unique |
| UnitExponent.polynomial_form | content | UnitExponent.approximation_stable | UnitExponent.generating_equation, UnitExponent.laurent_identity |
| UnitExponent.polynomial_unique | content | UnitExponent.polynomial_unique | UnitExponent.generating_unique |
| UnitExponent.laurent_normalization | bind-only | none | UnitExponent.laurent_window |
| UnitExponent.laurent_window | bind-only | none | UnitExponent.equation_of_laurent, UnitExponent.generating_equation |
| UnitExponent.laurent_identity | content | UnitExponent.approximation_stable | UnitExponent.generating_equation |
| UnitExponent.generating_equation | content | UnitExponent.approximation_stable | result |
| UnitExponent.equation_of_laurent | bind-only | none | UnitExponent.generating_unique |
| UnitExponent.generating_unique | content | UnitExponent.approximation_stable | result |
| UnitExponent.coefficient_four_dvd | content | UnitExponent.approximation_stable | UnitExponent.hanna_conjecture_general |
| UnitExponent.hanna_conjecture_general | content | UnitExponent.approximation_stable | result |
| result | content | UnitExponent.approximation_stable |  |

## Falsifier

A normalized integral solution and a positive index with residue different from two would contradict `result`. A failure of coefficient-window stabilization or of the contraction's agreement improvement would invalidate the stated route. Existence is included in the result, so an empty solution class cannot account for the universal assertion.

## Evidence

- Lean source: `D5/S1/Recurrence/Bilateral/BilateralProductModFourUnitExponent.lean`.
- Public theorem: `D5.S1.Recurrence.Bilateral.BilateralProductModFourUnitExponent.result`.
- Source note: `Library/RecurrenceComposition/hanna2025a380066.md`.
- Blueprint: `Blueprint/D5/S1/Recurrence/Bilateral/BilateralProductModFourUnitExponent.md`.
- Escape audit: [#20261](https://github.com/the-omega-institute/trureturing/issues/20261). The typed Reg mirror compiles and decodes, but the scoped registration record is `declared_unresolved`: `IE-C050 ClosedTruthReadout`, rule `source.selection_missing`. The missing evidence is a lawful source selection tying the coefficient readout to the original theorem occurrence. This is an unfinished escape audit, not `declared_validated`.

### Experiment

[Experiment directory at commit `584498b6e7361c4a77982c13222ecd2d1f8e4eac`](https://github.com/the-omega-institute/trureturing-experiments/tree/584498b6e7361c4a77982c13222ecd2d1f8e4eac/docs/reports/oeis-a380066-hanna-bilateral-mod-four). Command: `python3 check.py`, run in that directory, exit 0. Script SHA-256: `808934e604c7f107351d28b262482e6e017061444458192e28667830f39a2a22`. The parameter-one solution matches the first ten source terms and has integral coefficients through degree 18, residue two for indices 1 through 18, and the geometric-series congruence through degree 18. The parameter-two check matches the first ten listed A381362 coefficients. These finite readings do not establish the uniform theorem.

## Triage

| Item | Status | Evidence kind and scope |
| --- | --- | --- |
| OEIS A380066 congruence under the binding window convention | proved | Kernel-checked `result`, all normalized integral solutions and every positive index. |
| Unique normalized integral solution | proved | Kernel-checked private `UnitExponent.generating_equation` supplies existence; `UnitExponent.generating_unique` supplies uniqueness, at $c=1$. |
| Uniform extension from $c\ge2$ to every $c\ge1$ | proved | Kernel-checked private `UnitExponent.generating_equation`, `UnitExponent.generating_unique` and `UnitExponent.hanna_conjecture_general`, with their explicit $1\le c$ hypothesis. |
| Checker through degree 18 and first ten source terms | computed | The pinned experiment entry above; command exit 0 and the stated script hash. |
| The OEIS symmetry question $x\leftrightarrow A$ | open | No assertion in this module answers the source's symmetry question. |
| Uniqueness among rational normalized solutions | open | Outside the integral carrier of the delivered claim and uniqueness theorem. |

### What the settlement shows

The decisive mechanism is coefficientwise contraction followed by the fixed-point identity modulo four. The zero-index denominator separates from an integral nonzero-index remainder, and the factor two forces the residue independently of $c$ once $c\ge1$. The private universal theorems therefore extend the frozen range $c\ge2$ to $c\ge1$, including the source's boundary value $c=1$.

The integral solution is unique. The proof makes no assertion about uniqueness among rational normalized solutions, the meaning of the symmetry $x\leftrightarrow A$, or a parameter-zero extension. The OEIS entry supplies no other result depending on the conjecture in the cited source text, so no further dependency consequence is claimed.

## ASSUMED-UNVERIFIED

Literature completeness is `ASSUMED-UNVERIFIED`. The bilateral interpretation is the explicit coefficientwise-window convention of #18805; no analytic summability or convergence assertion is made. Rational uniqueness, the symmetry question, and parameter zero remain outside this settlement.
