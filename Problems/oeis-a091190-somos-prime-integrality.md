---
slug: oeis-a091190-somos-prime-integrality
bibkey: hanna2004a091190
doi: null
url: https://oeis.org/A091190
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/SomosPrimeIntegrality
---

# The Somos prime integrality family in OEIS A091190/A091200

## Problem

> More generally, given A(x) satisfies x*A(x)^p = B(x*A(x^p)) where B(x) = x/(1-p*x), then it appears that A(x) is an integer series only when p is prime.

For every natural $p\geq2$, a rational solution with $A(0)=1$ exists for $xA(x)^p=B(xA(x^p))$, where $B(x)=x/(1-px)$. Every such solution has integer coefficients if and only if $p$ is prime. The coefficientwise expression for $B$ is inlined in `IsGF`.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| x*A(x)^p = B(x*A(x^p)) | IsGF preserves the outer and inner substitutions | exact registered convention |
| B(x)=x/(1-p*x) | IsGF inlines coefficient zero at n=0 and p to the power n-1 otherwise | exact registered convention |
| offset-zero first term one | IsGF requires constant coefficient one | exact registered convention |
| integer only when prime | claim proves equivalence with primality for every normalized solution | exact registered convention |
| exponents in the registered domain | claim requires p at least two and asserts rational existence | exact registered convention |

## Motivation

The externally stated OEIS conjecture is preregistered in #18793. The settling declaration is `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.result`; its admission basis is `open-problem-resolution (#18793; Proved)`.

## Gap

The preregistration records the OEIS source and literature screen. The checked entries cite no proof. Literature-screen completeness is ASSUMED-UNVERIFIED. The mathematical gap is discharged by the settling declaration under the displayed coefficient rings and normalizations.

## Route

The geometric denominator identity gives the residual $A^p(1-pxA(x^p))-A(x^p)$. Prime Frobenius congruence makes integral corrections possible through the shared lifting construction. At a composite exponent the low-degree differential recurrence gives a contradiction modulo the least prime divisor. `General.prime_of_integral` is the necessity step used by `result`.

## Falsifier

A prime exponent with a nonintegral normalized solution or a composite exponent with an integral normalized solution contradicts `result`.

## Evidence

The Lean module and its Blueprint Scribe carry the exact statement. The axiom closure is contained in {propext, Classical.choice, Quot.sound}. The frozen module record is `Golden/Frozen/state/D5/S1/Recurrence/Invariants/SomosPrimeIntegrality.lean.json`. Escape audit unfinished: [#19794](https://github.com/the-omega-institute/trureturing/issues/19794); no compiled registration is delivered.

Publicized owner audit targets under [#19794](https://github.com/the-omega-institute/trureturing/issues/19794): `D5.S1.Recurrence.Invariants.AbsoluteReciprocalGeometricParity.agree_mul`; `D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity.agree_iff`; `D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity.agree_pow`; `D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity.agree_subst_order`; `D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity.power_two_one`. Four-slot registration is unfinished for each target.

### Experiment

[Pinned experiment](https://github.com/the-omega-institute/trureturing-experiments/tree/4f5fdee4b0fe08a512b072d264bbf641df28af57/docs/reports/oeis-a091190-somos-prime-integrality). Command: `python3 check.py` in that directory; exit 0; script SHA-256 `4af4904971adab029c3b7b91644f6a4ab789f41c203eff909726101f246257e5`.

Computed: for prime $p\leq29$, integrality holds through order 14 when $p<10$ and through order 8 otherwise. For composite $p\leq30$, the first noninteger coefficient occurs at the least prime factor $q$ and equals $\prod_{i<q}(1+ip)/q!$. At $p=25$ the value is $424099/5$. The first 14 terms match A091190 and A091200.

### Declaration classification

Same-delivery helpers are expanded for classification; consumed bind-only helpers are proof organization. The table names live consumers and the surviving construction or induction witness.

| Declaration | proof_shape | escape_witness | Direct proof-value consumers |
| --- | --- | --- | --- |
| `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.IsGF` | bind-only | `none` | `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.claim`, `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.isGF_iff`, `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.result` |
| `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.claim` | bind-only | `none` |  |
| `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.subst_one_series` | bind-only | `none` | `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General.low_order`, `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General.residual_base`, `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.isGF_iff` |
| `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General.residual` | bind-only | `none` | `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General.exists_integral`, `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General.exists_rational`, `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General.exists_solution_of_correction`, `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General.low_order`, `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General.low_recurrence`, `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General.map_residual`, `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General.prime_of_integral`, `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General.residual_agree`, `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General.residual_base`, `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General.residual_divisible`, `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General.residual_top`, `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General.unique`, `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.isGF_iff`, `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.result` |
| `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General.twist_agree` | bind-only | `none` | `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General.residual_agree`, `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General.residual_top` |
| `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General.unit_power_top` | bind-only | `none` | `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General.residual_top` |
| `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General.residual_agree` | bind-only | `none` | `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General.exists_solution_of_correction` |
| `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General.residual_top` | bind-only | `none` | `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General.exists_solution_of_correction`, `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General.unique` |
| `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General.residual_base` | bind-only | `none` | `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General.exists_solution_of_correction` |
| `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General.exists_solution_of_correction` | content | `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.Lifting.exists_lifted` | `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General.exists_integral`, `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General.exists_rational` |
| `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General.unique` | content | `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General.unique` | `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.result` |
| `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General.residual_divisible` | bind-only | `none` | `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General.exists_integral` |
| `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General.exists_integral` | content | `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.Lifting.exists_lifted` | `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.result` |
| `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General.exists_rational` | content | `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.Lifting.exists_lifted` | `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.result` |
| `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.B_equation` | bind-only | `none` | `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.isGF_iff` |
| `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.isGF_iff` | bind-only | `none` | `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.result` |
| `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General.map_residual` | bind-only | `none` | `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.result` |
| `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General.low_order` | bind-only | `none` | `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General.low_recurrence` |
| `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General.low_recurrence` | bind-only | `none` | `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General.prime_of_integral` |
| `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General.prime_of_integral` | content | `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General.prime_of_integral` | `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.result` |
| `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.result` | content | `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General.prime_of_integral` |  |

## Triage

| Item | Status | Evidence kind |
| --- | --- | --- |
| Rational existence and integrality iff primality (#18793) | proved | kernel-checked `result` |
| The same lifting mechanism for Hanna (#18792) | proved | kernel-checked `HannaPrimeSubstitutionIntegrality.result` |
| Cubic dyadic parity (#18788) | proved | kernel-checked `HannaA377106ParityReversion.result` |
| First failure at the least prime factor for composites up to 30 | computed | pinned experiment; exact scope above |
| Uniform first-noninteger coefficient formula | open | not a statement of a delivered theorem |
| General Somos equation for other B | open | outside the registered claim |
| Mathematical remaining goals for the three registered settlements | proved | the three result declarations discharge the registered claims |

### What the settlement shows

Proved in Lean: the assertion covers every exponent $p\geq2$ and every normalized rational solution, with rational existence for all those exponents and both directions of integrality iff primality. The low-degree obstruction supplies the necessary direction. A uniform location or formula for the first noninteger coefficient remains outside the formal conclusion.

## ASSUMED-UNVERIFIED

Literature completeness and originality are not established. The other source families and uniform extensions marked open above are outside this settlement. Four-slot escape registration remains unfinished under #19794.
