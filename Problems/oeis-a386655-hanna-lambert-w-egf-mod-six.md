---
slug: oeis-a386655-hanna-lambert-w-egf-mod-six
bibkey: hanna2025a386655a386658
doi: null
url: https://oeis.org/A386655
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/HannaLambertW/OeisA386655LambertWEgfModSix.result
  - D5/S3/Combinatorics/HannaLambertW/OeisA386656LambertWEgfModSix.result
  - D5/S3/Combinatorics/HannaLambertW/OeisA386657LambertWEgfModSix.result
  - D5/S3/Combinatorics/HannaLambertW/OeisA386658LambertWEgfModSix.result
---

# Hanna's Lambert W coefficient congruences

## Problem

Preregistration: [#18668](https://github.com/the-omega-institute/trureturing/issues/18668).
Paul D. Hanna's OEIS A386655 NAME reads: "E.g.f.: Sum_{n>=0} (2^n*x + LambertW(x))^n / n!."
Its COMMENTS sentence is: "Conjecture: for n >= 6, a(n) (mod 6) equals [1, 0, 3, 0, 3, 2] repeating."
The corresponding entries A386656, A386657 and A386658 replace $2$ by $3$, $4$ and $5$, respectively.
Their COMMENTS sentences specify $[4,3,2,1,0,1]$, $[1,2,3,2,3,4]$ and $[4,3,0,3,0,5]$.
All four statements include integrality and the index $(n-6)\bmod6$ for every natural $n\ge6$.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Principal formal Lambert W | `OeisA386655LambertWEgfModSix.W` | Constant coefficient zero and positive coefficient $(-m)^{m-1}/m!$. |
| Exponential generating coefficient | `egf q m` | $m!$ times the coefficient of $x^m$; summation through $m$ is exact because each later summand has order greater than $m$. |
| Bases $q=2,3,4,5$ | Each module's `a` | The respective `egf` specialization. |
| Every $n\ge6$ | Each module's `claim` and `result` | Universal natural index and the literal lower bound. |
| Integral remainder with the published pattern | Each module's `claim` and `result` | An integer representative with rational cast equal to `a n`, and integer remainder equal to the zero-based `List.getD` entry. |
| Finite-sum endpoint | `closedZ q n` | The source's last summand is $q^{n^2}$; all remaining exponents are natural numbers. |

The public definitions retain the preregistered expressions. The formal series interpretation makes no assertion about analytic convergence or values outside that series.

## Motivation

The four result declarations settle the four explicitly published congruence conjectures. The shared module also establishes integrality for every natural base and every coefficient, and a uniform six-term reduction for every natural base above the sixth index.

## Gap

The classical Abel–Lagrange exponential-of-W identity and the finite-ring binomial calculation supply the proof route. These classical ingredients are not asserted to be new. Literature-search completeness is `ASSUMED-UNVERIFIED`; the bounded screen recorded in #18668 found no settlement of the four named conjectures.

## Route

The shared module uses `NonnestingOneThreeTwoTwo.lagrange_coefficient` to compute the coefficients of an exponential after substitution into the inverse of `QuarticEGFModFour.F`. Its private `T_eq_W` identifies that inverse with the literal series `W`. Triangular reindexing and binomial expansion give `egf_closed` and its integral finite sum.

For the modulus, the identity $x^3=x$ in $\mathbb Z/6\mathbb Z$ reduces positive powers. Pascal expansion gives the binomial-transform relation $B(n+9)=B(n+3)$, and the endpoint corrections depend only on the index modulo six. `closedZ_reduce` turns this into an integer-remainder identity. The four results combine the integral formula with the six values at indices $6$ through $11$.

The coefficient-substitution supplier is the published existing `TripleIterateShiftModThree.subst_coeff`, directly consumed by the shared module. Its statement and proof retain the existing substitution formula.

## Falsifier

An index $n\ge6$ with a nonintegral coefficient, or a remainder differing from the corresponding six-entry list, contradicts the relevant `result`. The explicit integer representative excludes a vacuous settlement. A failure of a finite experiment is a test of the stated computational scope; the universal conclusions are the Lean declarations.

## Evidence

- Lean owners: `D5/S3/Combinatorics/HannaLambertW/OeisA386655LambertWEgfModSix.lean`, `OeisA386656LambertWEgfModSix.lean`, `OeisA386657LambertWEgfModSix.lean` and `OeisA386658LambertWEgfModSix.lean` in the same directory.
- Settling declarations: each owner's `result`.
- General shared conclusions: `OeisA386655LambertWEgfModSix.egf_closed` and `OeisA386655LambertWEgfModSix.closedZ_reduce`.
- Source note: `Library/RecurrenceComposition/hanna2025a386655a386658.md`.
- Every newly authored or published theorem is classified `bind-only`, with `escape_witness: none`. Each settlement module has admission basis `open-problem-resolution (#18668; Proved)`. Finite-ring identities and the six starting values are consumed normalization steps within unbounded symbolic conclusions; all five reviewed modules have `utility: none`.
- The four-slot escape audit is unfinished under [#19849](https://github.com/the-omega-institute/trureturing/issues/19849) for the four results, `egf_closed`, `closedZ_reduce` and the published `TripleIterateShiftModThree.subst_coeff`. Source reconstruction, a lawful enrolled readout, a typed realization bridge, whole-family intervention/sensitivity and actual observational-dependence evidence are absent. No validated registration is asserted.

### Declaration classifications

The table reports the compiled declaration graph after expanding generated implementation declarations. Definitions have no theorem proof shape. All theorem rows have `escape_witness: none`; settling results are admitted through the named external problem.

| Declaration | proof_shape | Direct consumers |
| --- | --- | --- |
| `D5.S1.Recurrence.Invariants.TripleIterateShiftModThree.subst_coeff` | bind-only | `D5.S1.Recurrence.Invariants.TripleIterateShiftModThree.iterate_normal`, `D5.S1.Recurrence.Invariants.TripleIterateShiftModThree.subst_inner_top`, `D5.S1.Recurrence.Invariants.TripleIterateShiftModThree.subst_outer_top`, `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.egf_closed`, `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.egf_rearranged`, `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.lagrange_subst` |
| `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.forward_unit` | bind-only | `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.T`, `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.T_inverse`, `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.T_zero` |
| `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.T_zero` | bind-only | `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.T_eq_W`, `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.T_equation`, `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.coeff_exp_W` |
| `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.T_inverse` | bind-only | `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.T_equation` |
| `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.T_equation` | bind-only | `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.T_eq_W`, `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.coeff_exp_W` |
| `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.E_mul` | bind-only | `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.coeff_exp_W` |
| `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.E_pow` | bind-only | `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.T_eq_W`, `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.coeff_exp_W` |
| `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.E_coeff` | bind-only | `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.T_eq_W`, `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.coeff_exp_W`, `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.derivative_E`, `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.egf_rearranged` |
| `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.T_eq_W` | bind-only | `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.coeff_exp_W` |
| `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.lagrange_subst` | bind-only | `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.coeff_exp_W` |
| `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.derivative_E` | bind-only | `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.coeff_exp_W` |
| `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.coeff_exp_W` | bind-only | `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.egf_closed` |
| `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.sum_triangle` | bind-only | `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.egf_rearranged` |
| `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.coeff_binomial` | bind-only | `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.egf_rearranged` |
| `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.factorial_ratio` | bind-only | `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.egf_rearranged` |
| `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.egf_rearranged` | bind-only | `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.egf_closed` |
| `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.egf_closed` | bind-only | `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.result`, `D5.S3.Combinatorics.HannaLambertW.OeisA386656LambertWEgfModSix.result`, `D5.S3.Combinatorics.HannaLambertW.OeisA386657LambertWEgfModSix.result`, `D5.S3.Combinatorics.HannaLambertW.OeisA386658LambertWEgfModSix.result` |
| `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.B_succ` | bind-only | `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.Bs_succ` |
| `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.Bs_succ` | bind-only | `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.B_period` |
| `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.B_period` | bind-only | `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.B_reduce` |
| `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.cube_eq` | bind-only | `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.pow_shift_two` |
| `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.pow_shift_two` | bind-only | `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.pow_positive` |
| `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.pow_positive` | bind-only | `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.pow_redPow` |
| `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.pow_redPow` | bind-only | `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.closedR_B`, `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.interior_weight` |
| `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.redPow_product` | bind-only | `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.closedR_B`, `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.interior_weight` |
| `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.redPow_square` | bind-only | `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.closedR_B` |
| `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.weight_top` | bind-only | `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.closedR_B` |
| `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.B_reduce` | bind-only | `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.closedR_reduce` |
| `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.interior_weight` | bind-only | `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.closedR_B` |
| `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.closedR_B` | bind-only | `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.closedR_reduce` |
| `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.closedR_reduce` | bind-only | `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.closedZ_reduce` |
| `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.closedZ_cast` | bind-only | `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.closedZ_reduce` |
| `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.closedZ_reduce` | bind-only | `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.pattern_2`, `D5.S3.Combinatorics.HannaLambertW.OeisA386656LambertWEgfModSix.result`, `D5.S3.Combinatorics.HannaLambertW.OeisA386657LambertWEgfModSix.result`, `D5.S3.Combinatorics.HannaLambertW.OeisA386658LambertWEgfModSix.result` |
| `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.values_2` | bind-only | `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.pattern_2` |
| `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.pattern_2` | bind-only | `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.result` |
| `D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.result` | bind-only | settling result |
| `D5.S3.Combinatorics.HannaLambertW.OeisA386656LambertWEgfModSix.values` | bind-only | `D5.S3.Combinatorics.HannaLambertW.OeisA386656LambertWEgfModSix.result` |
| `D5.S3.Combinatorics.HannaLambertW.OeisA386656LambertWEgfModSix.result` | bind-only | settling result |
| `D5.S3.Combinatorics.HannaLambertW.OeisA386657LambertWEgfModSix.values` | bind-only | `D5.S3.Combinatorics.HannaLambertW.OeisA386657LambertWEgfModSix.result` |
| `D5.S3.Combinatorics.HannaLambertW.OeisA386657LambertWEgfModSix.result` | bind-only | settling result |
| `D5.S3.Combinatorics.HannaLambertW.OeisA386658LambertWEgfModSix.values` | bind-only | `D5.S3.Combinatorics.HannaLambertW.OeisA386658LambertWEgfModSix.result` |
| `D5.S3.Combinatorics.HannaLambertW.OeisA386658LambertWEgfModSix.result` | bind-only | settling result |

### Experiment

[Exact coefficient and congruence checker](https://github.com/the-omega-institute/trureturing-experiments/tree/b8ebb8ab99d203d2bf922214bc89be78c0effbf5/docs/reports/oeis-a386655-a386658-lambert-w-egf-mod-six), commit `b8ebb8ab99d203d2bf922214bc89be78c0effbf5`. Command: `python3 check.py 12 400` in that directory, exit 0. Script SHA-256: `2083fed63d33e2bd370a7b7906f56af4abe4f21187272845064de6e8a0ca372c`. For each base $q=2,3,4,5$, the closed form agrees with exact series expansion for $0\le n\le12$ and with the source data. The four patterns hold for $6\le n\le400$ and for $n=3,4,5$. The finite-ring polynomial identities $(1+x)^9=(1+x)^3$ modulo $(x^6-1,3)$ and $(1+x)^2=0$ modulo $(x^2-1,2)$ pass. These are computed finite readings.

## Triage

| Lane target item | Status | Evidence kind and boundary |
| --- | --- | --- |
| All four named targets | Proved | Kernel-checked `result` in each of the four Hanna modules. |
| Exponential-of-W coefficient identity (M1) | Proved | Kernel-checked private `OeisA386655LambertWEgfModSix.coeff_exp_W`, using `T_eq_W` and frozen Lagrange inversion. |
| Integral closed form (M2) | Proved | Kernel-checked `egf_closed`, for every natural $q,n$. |
| Six-term modular reduction (M3) | Proved | Kernel-checked `closedZ_reduce`, for every natural $q$ and $n\ge6$. |
| Assembly (M4) | Proved | Kernel-checked four `result` declarations and the consumed six-value lemmas. |
| Admission and escape witness | Proved settlement | Kernel-checked `result` under the external-settlement admission #18668. The independent proof-shape judgement is bind-only with no escape witness; this classification is not a Lean novelty theorem. |
| Private substitution supplier | Proved interface use | Kernel-checked direct applications of the published `TripleIterateShiftModThree.subst_coeff` in `egf_rearranged` and `egf_closed`. |
| Numerical checker | Computed | The pinned experiment and exact tested scope above. |
| Pattern from index three | Computed | The experiment checks indices $3,4,5$ as well as its displayed finite range. A uniform Lean theorem with lower bound three is open in this delivery. |
| Literature status | Open | The source and bounded literature screen in #18668; completeness `ASSUMED-UNVERIFIED`. |

### What the settlement shows

**Kernel-checked:** the decisive mechanism is the integral coefficient identity plus finite-ring binomial periodicity. `egf_closed` extends integrality to every natural base and every index; `closedZ_reduce` extends the modular reduction to every natural base for $n\ge6$. The four `result` declarations give exactly the four published lists.

**Computed:** the pinned checker tests the four patterns from index three within its stated finite scope. **Open:** no Lean result here lowers the uniform threshold from six to three, proves an optimal threshold, or gives analytic convergence. These extensions are not required for the four conjectures.

The four named source conjectures require no remaining conditional congruence assumption. The classical coefficient identity and source formulas are explained by the shared argument; no additional dependent theorem from the source is claimed.

## ASSUMED-UNVERIFIED

Literature completeness, publication priority and analytic interpretation beyond formal power series are not kernel conclusions. Bounded `exact?` searches and textual owner searches do not establish exhaustive absence of an owner. The finite experiment does not prove an unbounded statement. The four-slot audit remains unfinished under #19849.
