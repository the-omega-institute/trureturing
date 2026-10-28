---
slug: oeis-a271931-hanna-prime-substitution-integrality
bibkey: hanna2016a271931
doi: null
url: https://oeis.org/A271931
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/HannaPrimeSubstitutionIntegrality
---

# Hanna's prime substitution integrality conjecture

## Problem

> More generally, for prime p there exists an integer series G(x) that satisfies: G(x) = G( x^p + p*x*G(x)^p )^(1/p) with G(0)=0, G'(0)=1 (conjecture).

For every prime $p$, there is $G\in\mathbb Z[[x]]$ with $G(0)=0$, $[x]G=1$, and $G^p=G(x^p+pxG^p)$. The entries A271931, A271932 and A271933 specialize to $p=5,7,11$. The powered equation expresses the normalized root convention.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| every prime exponent | claim quantifies over natural p with Nat.Prime | exact registered convention |
| integer series | the existential series has coefficient ring integers | exact registered convention |
| G(0)=0 and G'(0)=1 | constant coefficient zero and coefficient one equal to one | exact registered convention |
| root equation | the pth-power substitution equation in claim | exact registered convention |

## Motivation

The externally stated OEIS conjecture is preregistered in #18792. The settling declaration is `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.result`; its admission basis is `open-problem-resolution (#18792; Proved)`.

## Gap

The preregistration records the OEIS source and literature screen. The checked entries cite no proof. Literature-screen completeness is ASSUMED-UNVERIFIED. The mathematical gap is discharged by the settling declaration under the displayed coefficient rings and normalizations.

## Route

Frobenius over $\mathbb Z/p\mathbb Z$ makes each residual coefficient divisible by $p$. The triangular first-difference formula makes the next coefficient correction exact. Coefficient stabilization defines a limiting integer series. `General.Lifting.exists_lifted` supplies the lifting construction; `General.exists_integral` applies it to every integer $c$ divisible by $p$.

## Falsifier

A prime $p$ without a normalized integral solution, or an invalid coefficient correction or stabilization step, contradicts the settlement.

## Evidence

The Lean module and its Blueprint Scribe carry the exact statement. The axiom closure is contained in {propext, Classical.choice, Quot.sound}. The frozen module record is `Golden/Frozen/state/D5/S1/Recurrence/Invariants/HannaPrimeSubstitutionIntegrality.lean.json`. Escape audit unfinished: [#19794](https://github.com/the-omega-institute/trureturing/issues/19794); no compiled registration is delivered.

Publicized owner audit targets under [#19794](https://github.com/the-omega-institute/trureturing/issues/19794): `D5.S1.Recurrence.Invariants.AbsoluteReciprocalGeometricParity.agree_mul`; `D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity.agree_iff`; `D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity.agree_pow`; `D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity.agree_subst_order`; `D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity.power_two_one`. Four-slot registration is unfinished for each target.

### Experiment

[Pinned experiment](https://github.com/the-omega-institute/trureturing-experiments/tree/c12f37d7f281f81b541d6cde08b5ff7a54079e96/docs/reports/oeis-a271931-hanna-prime-substitution-integrality). Command: `python3 check.py` in that directory; exit 0; script SHA-256 `dbca23c21bd0e345f18b8bfaf6a16a0b72fef1d36ba60dd7e3d28232192e5f68`.

Computed: for $p=2,3,5,7,11,13,17,19,23$, exact divisions and the functional equation hold through orders $30,30,30,25,20,18,14,13,12$, respectively. The first 12 terms match A271931/A271932/A271933. For composite $p=4,6,8,9$, the first nonintegral reversion coefficients are $r_3=-1/2,-3/2,-5/2$ and $r_4=-35/3$, respectively.

### Declaration classification

Same-delivery helpers are expanded for classification; consumed bind-only helpers are proof organization. The table names live consumers and the surviving construction or induction witness.

| Declaration | proof_shape | escape_witness | Direct proof-value consumers |
| --- | --- | --- | --- |
| `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.claim` | bind-only | `none` |  |
| `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.power_factor` | bind-only | `none` | `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.agree_power_order`, `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.power_top` |
| `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.agree_power_order` | bind-only | `none` | `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.inner_agree`, `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.residual_agree` |
| `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.power_top` | bind-only | `none` | `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.residual_top` |
| `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.inner` | bind-only | `none` | `D5.S1.Recurrence.Invariants.HannaA377106ParityReversion.map_solution`, `D5.S1.Recurrence.Invariants.HannaA377106ParityReversion.result`, `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.inner_agree`, `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.inner_zero`, `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.residual`, `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.residual_agree`, `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.residual_base`, `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.residual_divisible`, `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.residual_top`, `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.rhs_agree`, `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.solution_unique` |
| `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.inner_zero` | bind-only | `none` | `D5.S1.Recurrence.Invariants.HannaA377106ParityReversion.map_solution`, `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.residual_base`, `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.residual_divisible`, `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.rhs_agree` |
| `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.inner_order` | bind-only | `none` | `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.rhs_agree` |
| `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.inner_agree` | bind-only | `none` | `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.rhs_agree` |
| `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.rhs_agree` | bind-only | `none` | `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.residual_agree`, `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.residual_top` |
| `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.residual` | bind-only | `none` | `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.exists_integral`, `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.exists_solution_of_correction`, `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.residual_agree`, `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.residual_base`, `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.residual_divisible`, `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.residual_top`, `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.solution_unique` |
| `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.residual_agree` | bind-only | `none` | `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.exists_solution_of_correction` |
| `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.residual_top` | bind-only | `none` | `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.exists_solution_of_correction`, `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.solution_unique` |
| `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.residual_divisible` | bind-only | `none` | `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.exists_integral` |
| `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.Lifting.extend` | bind-only | `none` | `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.Lifting.approximation`, `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.Lifting.approximation_spec`, `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.Lifting.approximation_stable`, `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.Lifting.extend_agree`, `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.Lifting.extend_spec` |
| `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.Lifting.extend_agree` | bind-only | `none` | `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.Lifting.approximation_stable`, `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.Lifting.extend_spec` |
| `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.Lifting.approximation` | bind-only | `none` | `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.Lifting.approximation_spec`, `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.Lifting.approximation_stable`, `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.Lifting.exists_lifted`, `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.Lifting.limitSeries`, `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.Lifting.limit_agree` |
| `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.Lifting.extend_spec` | bind-only | `none` | `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.Lifting.approximation_spec` |
| `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.Lifting.approximation_spec` | content | `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.Lifting.approximation_spec` | `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.Lifting.exists_lifted` |
| `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.Lifting.approximation_stable` | content | `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.Lifting.approximation_stable` | `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.Lifting.limit_agree` |
| `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.Lifting.limitSeries` | bind-only | `none` | `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.Lifting.exists_lifted`, `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.Lifting.limit_agree` |
| `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.Lifting.limit_agree` | content | `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.Lifting.limit_agree` | `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.Lifting.exists_lifted` |
| `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.Lifting.exists_lifted` | content | `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.Lifting.exists_lifted` | `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.exists_solution_of_correction`, `D5.S1.Recurrence.Invariants.SomosPrimeIntegrality.General.exists_solution_of_correction` |
| `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.normal_of_agree` | bind-only | `none` | `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.exists_solution_of_correction` |
| `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.residual_base` | bind-only | `none` | `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.exists_solution_of_correction` |
| `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.exists_solution_of_correction` | content | `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.Lifting.exists_lifted` | `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.exists_integral` |
| `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.solution_unique` | content | `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.solution_unique` | `D5.S1.Recurrence.Invariants.HannaA377106ParityReversion.result` |
| `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.exists_integral` | content | `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.Lifting.exists_lifted` | `D5.S1.Recurrence.Invariants.HannaA377106ParityReversion.result`, `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.result` |
| `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.result` | content | `D5.S1.Recurrence.Invariants.HannaPrimeSubstitutionIntegrality.General.Lifting.exists_lifted` |  |

## Triage

| Item | Status | Evidence kind |
| --- | --- | --- |
| Prime substitution conjecture (#18792) | proved | kernel-checked `result` |
| Integral extension to any integer c divisible by p | proved | kernel-checked `General.exists_integral` |
| Normalized uniqueness with nonzero exponent coefficient over a ring without zero divisors | proved | kernel-checked `General.solution_unique` |
| A377106 integrality and parity (#18788) | proved | kernel-checked `HannaA377106ParityReversion.result` |
| Somos integrality iff primality (#18793) | proved | kernel-checked `SomosPrimeIntegrality.result` |
| Composite Hanna examples p=4,6,8,9 | computed | pinned experiment; reversion coefficients and scope above |
| Catalan comparison at p=2,3 | computed | pinned experiment through order 30; an unbounded Catalan identification is open in this delivery |
| Mathematical remaining goals for the three registered settlements | proved | the three settling result declarations discharge the registered claims |
| Uniform Hanna composite-exponent necessity, a least-noninteger coefficient formula, and other Somos B families | open | outside the three result statements |

### What the settlement shows

Proved in Lean: the integral construction allows every integer $c$ divisible by $p$; uniqueness applies over any commutative ring without zero divisors when the exponent coefficient is nonzero. The conjectural existence comments in the three entries are established with their stated normalization. The composite examples and Catalan comparison remain computations at the scopes above.

## ASSUMED-UNVERIFIED

Literature completeness and originality are not established. The other source families and uniform extensions marked open above are outside this settlement. Four-slot escape registration remains unfinished under #19794.
