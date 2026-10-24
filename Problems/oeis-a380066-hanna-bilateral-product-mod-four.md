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

The source is an explicitly stated, externally published conjecture (tier 1). The settling GID is `D5/S1/Recurrence/Bilateral/BilateralProductModFourUnitExponent.result`. Its proof shape is **bind-only**. The requested admission basis is `open-problem-resolution (#18805; Proved)`, whose literature condition remains unverified. The preregistration contains the literal source, complete binding conventions, tier and screen, and predates the original delivery; its existence alone does not discharge that condition. The candidate pin records compiled identity and supplies no admission exception. Its Scribe contains one `OpenProblemResolutionClaim`, with resolution `Proved`, describing mathematical truth rather than admission completion. This delivery remains Draft mathematical WIP for admission.

## Gap

The frozen `BilateralProductModFour` family supplies the summands and series construction, but its generating-equation, uniqueness and congruence theorems assume $2\le c$. Those hypotheses do not cover $c=1$.

The current OEIS internal entry retains the literal name, conjecture and offset, and contains no proof of the conjecture. The literature screen recorded in #18805 reads the OEIS entry. The search producer reports checking classical bilateral summations (DLMF sections 17.8 and 20.5), Schlosser's arXiv:math/0302270 and Kallat's arXiv:2610.15849; those readings are producer-reported. Strehl, Discrete Mathematics 99 (1992), is not read. The current bounded screen also reads DLMF sections 17.8 and 20.5, Schlosser's arXiv:math/0302270v4, Theorem 4.1 and Corollary 4.2, and the text of Kallat's arXiv:2610.15849. The DLMF sections state bilateral hypergeometric and theta product identities; no correspondence to this implicit integral-series congruence is established. Schlosser's two identities use infinite q-shifted products and require the stated parameter conditions; no specialization to this implicit integral-series congruence is established. These selected results are not a verification of the complete paper. Kallat's text concerns weighted permutation shift congruences and contains no A380066 occurrence; no reduction of this problem to its hypotheses is established. These limited readings do not close the missing literature obligation. Completeness remains `ASSUMED-UNVERIFIED`; in particular the complete Schlosser reduction and Strehl reference have not been verified. The latter is Strehl, “Identities of Rothe–Abel–Schläfli–Hurwitz-type”, Discrete Mathematics 99 (1992), 321–340, DOI `10.1016/0012-365X(92)90379-T`; publisher full text returned HTTP 403 and the alternate text endpoint returned HTTP 400. Search-engine responses supplied a bot challenge or unrelated results, and are not a completed literature search.

## Route

For each $c\ge1$, write the nonzero-index remainder as $H=S_c(A)$. Positive summands have order at least their positive index; the negative summand at $-m$ has order at least $cm^2\ge m$. The private `term_order`, `outside_zero` and `finite_window` give coefficientwise finite windows. The consumed private contraction lemmas show that the fixed-point step improves agreement by one degree. The induction in `UnitExponent.approximation_stable` stabilizes the existing approximations; `generating_fixed` and `generating_equation` establish the normalized integral solution. The private `polynomial_unique` directly applies frozen `PowerSeriesNormalizedContraction.exists_unique_fixed` over $\mathbb Z$ to `step c`. The normalization premise follows from `step_zero`, even without normalized input; the strict-contraction premise follows from `step_agree`, even without the generic theorem's restrictions to normalized inputs and positive degree. Both agreement predicates unfold to equality of coefficients below the degree. The generic uniqueness projection identifies the arbitrary normalized solution and the constructed `generatingSeries c` with the same witness; `polynomial_form` and `generating_fixed` certify the latter's premises. `generating_unique` transfers the literal Laurent equation to that polynomial fixed-point equation.

At the fixed point, $(1+x)(1+A)(1-2H)=2$. The private `coefficient_four_dvd` establishes divisibility by four of the difference from $2/(1+x)-1$, coefficientwise. `hanna_conjecture_general` yields residue two at every positive index for all $c\ge1$; `result` specializes to the source's parameter one and transports the conclusion to every normalized integral solution.

### Declaration classification

The table expands the same-delivery helper graph to frozen and pinned-upstream boundaries, including `PowerSeriesNormalizedContraction.exists_unique_fixed` on the protected baseline (module statement identity `sha256:6fde09331cce748985c92e44cd8bb294c09eb2f01eeea1d646183f03ab04baf4`). Names are relative to the module namespace. Construction statements name the specified approximations, diagonal series or its coefficients, and depend on `approximation_stable`. In contrast, `result` merely asserts existence and a property of every solution: the generic theorem can supply its witness, and the equation correspondence and coefficient algebra then give the claim by binding and normalization. Thus the construction is useful, but is not an escape witness for `result`. The terminal bind-only declaration requires the external-problem exception; admission remains pending its missing literature evidence.

| declaration | proof_shape | escape_witness | direct consumers |
| --- | --- | --- | --- |
| UnitExponent.term_order | bind-only | none | UnitExponent.outside_zero |
| UnitExponent.outside_zero | bind-only | none | UnitExponent.finite_window |
| UnitExponent.finite_window | bind-only | none | UnitExponent.laurent_window, UnitExponent.sum_zero |
| UnitExponent.sum_zero | bind-only | none | UnitExponent.step_agree, UnitExponent.step_zero |
| UnitExponent.term_agree | bind-only | none | UnitExponent.sum_agree |
| UnitExponent.sum_agree | bind-only | none | UnitExponent.step_agree |
| UnitExponent.step_zero | bind-only | none | UnitExponent.polynomial_form, UnitExponent.polynomial_unique |
| UnitExponent.step_agree | bind-only | none | UnitExponent.approximation_stable, UnitExponent.generating_fixed, UnitExponent.polynomial_unique |
| UnitExponent.approximation_stable | content | UnitExponent.approximation_stable | UnitExponent.generating_agree |
| UnitExponent.generating_agree | content | UnitExponent.approximation_stable | UnitExponent.generating_fixed |
| UnitExponent.generating_fixed | content | UnitExponent.approximation_stable | UnitExponent.coefficient_four_dvd, UnitExponent.polynomial_form, UnitExponent.polynomial_unique |
| UnitExponent.polynomial_form | content | UnitExponent.approximation_stable | UnitExponent.generating_equation, UnitExponent.laurent_identity |
| UnitExponent.polynomial_unique | content | UnitExponent.approximation_stable | UnitExponent.generating_unique |
| UnitExponent.laurent_normalization | bind-only | none | UnitExponent.laurent_window |
| UnitExponent.laurent_window | bind-only | none | UnitExponent.equation_of_laurent, UnitExponent.generating_equation |
| UnitExponent.laurent_identity | content | UnitExponent.approximation_stable | UnitExponent.generating_equation |
| UnitExponent.generating_equation | content | UnitExponent.approximation_stable | result |
| UnitExponent.equation_of_laurent | bind-only | none | UnitExponent.generating_unique |
| UnitExponent.generating_unique | content | UnitExponent.approximation_stable | result |
| UnitExponent.coefficient_four_dvd | content | UnitExponent.approximation_stable | UnitExponent.hanna_conjecture_general |
| UnitExponent.hanna_conjecture_general | content | UnitExponent.approximation_stable | result |
| result | bind-only | none | none |

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

The bind-only terminal result has no verified §3.2 admission exception while literature completeness is `ASSUMED-UNVERIFIED`. This is an admission gap, independent of the kernel-checked statement and the unfinished §3.9 audits. The bilateral interpretation is the explicit coefficientwise-window convention of #18805; no analytic summability or convergence assertion is made. Rational uniqueness, the symmetry question, and parameter zero remain outside this settlement.

The public agreement, geometric-series, fixed-point and Laurent correspondence interface is
owned by `D5/S1/Recurrence/Bilateral/BilateralProductModFour`. Its original statements and
proofs are reused directly. The four-slot audits for `agree_iff`, `agree_refl`, `agree_add`,
`agree_mul`, `agree_pow`, `agree_inverse`, `agree_shift`, `geometric_spec`, `geometric_coeff`,
`equation_iff`, `embed_coeff`, `embed_injective`, `embed_inverse`, `negative_factorization`,
`laurent_zero` and `zeroTerm_series` are unfinished under
[#20261](https://github.com/the-omega-institute/trureturing/issues/20261): no complete
source telescope reconstruction, lawful source selection and whole-family sensitivity
evidence is supplied for these public interface theorems. The existing audit of
`ofSeries_inverse` remains unfinished under
[#19114](https://github.com/the-omega-institute/trureturing/issues/19114).
