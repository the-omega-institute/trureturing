---
slug: op-ahrami2605gap
bibkey: ahrami2026weightedgap
doi: 10.48550/arXiv.2605.24560
triage: theorem
motivation_gids:
  - D5/S3/Analytic/SpectralGap/WeightedConvexPotentialRefutation.result
url: https://arxiv.org/abs/2605.24560v1
---

# Ahrami Open Problem 3.3: weighted convex-potential spectral gaps

## Problem

Mohammed Ahrami, *On the fundamental spectral gap of weighted Schrodinger operators*, arXiv:2605.24560v1, Open Problem 3.3, Section 3.2:

> Let $w$ be a positive concave weight on $[0,\pi]$. Does the constant potential minimzer the fundamental spectral gap over the class of convex potentials. Equivalently,
>
> $$\Gamma[V,w]\geq \Gamma[0,w]$$
>
> for every convex potential $V$.

The binding Lean proposition is `WeightedGapPolynomialCertificate.claim`; its negation is the settling declaration `WeightedConvexPotentialRefutation.result`. The index $0$ is $\lambda_1$ and index $1$ is $\lambda_2$, and both min-max spectra are quantified as existing.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Positive concave bounded weight on $[0,\pi]$ | `weightClass Nlo Nhi w` | Includes bounded measurability, concavity, and the two pointwise bounds. |
| Convex potential class in Definition 3.1 | `potentialClass M V` | Includes bounded measurability, convexity, nonnegativity, and the `WithTop ℝ` upper bound. |
| Weighted Dirichlet spectrum exists | `isSpectrum V w e` and `isSpectrum (fun _ => 0) w e0` | Nonempty and bounded-below min-max upper-bound sets are explicit. |
| Fundamental gap | `gap e = e 1 - e 0` | Index convention matches $\lambda_2-\lambda_1$. |
| Universal comparison | `claim`; `result : ¬ claim` | All source quantifiers and hypotheses are retained. |

## Motivation

The settlement addresses the displayed comparison in Open Problem 3.3. It uses the fixed affine potential $V(x)=x/100$, the positive affine concave weight $w(x)=1+(x-\pi/2)/100$, and $M=2$, $N_{<}=1/2$, $N_{>}=3/2$. The module has `generality: I` and `utility: kind=certified-instance; basis=refutes=...`.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9). Supporting public audit targets remain unfinished under [#27756](https://github.com/the-omega-institute/trureturing/issues/27756); no `declared_validated` status is claimed without the required CI reading.

## Gap

The source comparison fails for the fixed affine pair. The strict negative gap difference is certified by four shooting-root brackets, a degree-80 rational interval certificate, the Volterra identity and the shooting/min-max bridge.

## Route

The coefficient recurrence is bounded by a geometric majorant. The determinant is continuous in the spectral parameter, and opposite endpoint signs produce four shooting roots. Form comparison localizes these roots to the first two min-max values for the zero and affine potentials. Subtracting the four certified intervals gives a strict negative gap difference.

## Falsifier

The settlement would fail if the class-membership bounds, determinant sign brackets, root ordering, shooting/min-max identification, or final interval subtraction were false. It does not claim an all-small-slope theorem, a perturbative expansion in Lean, or a minimizer statement for every ordinary constant potential.

## Evidence

The settling module is `D5/S3/Analytic/SpectralGap/WeightedConvexPotentialRefutation.lean`; its direct D5 inputs are `WeightedGapPolynomialCertificate`, `WeightedGapMajorant`, `WeightedGapStateSeries`, `WeightedGapDeterminant`, `WeightedGapVolterra`, and the frozen `MomentOrthogonalPrimitiveGap` declaration used by the bridge. The scoped Lean build and report both exit 0. The result has axiom closure contained in `{propext, Classical.choice, Quot.sound}`.

### Experiment

The exact external checker is pinned at [the experiments repository](https://github.com/the-omega-institute/trureturing-experiments/tree/52aded4b71359d83032e504d3d877b5a8aa9322c/docs/reports/weighted-gap-convex-potential), commit `52aded4b71359d83032e504d3d877b5a8aa9322c`. The command `python3 /Users/auric/.op-scratch/op/op-ahrami2605gap-stageb/check.py` exits 0 and ends with `ALL_CHECKS_OK`; `check.py` SHA-256 is `70ca2ca848f61a5e19b80e3f60370ba79528f961c9f64a5c8678e7e3a776514a`. Its finite scope checks the class bounds, degree-160 Taylor remainder, four root brackets, ordering localization, and strict gap interval.

### Literature boundary

The source/version and related-literature screen recorded in issue #27107 is partial. Completeness of the priority and citation search is `ASSUMED-UNVERIFIED`. The unweighted Lavine theorem and the cited Stark expansion are literature-attested and outside the weighted counterexample's scope.

## Triage

### What the settlement shows

| Item | Status and evidence kind | Result and boundary |
| --- | --- | --- |
| Fixed affine potential and positive affine weight satisfy the binding classes with $M=2$, $N_{<}=1/2$, $N_{>}=3/2$ | Proved; kernel-checked `fixed_potential_class` and `fixed_weight_class` | The pair is convex/concave, bounded and strictly positive on the interval. |
| Exact checker derives perturbative gap coefficient $-(45+4\pi^2)/256$ | Computed; pinned experiment command, exit 0, script SHA-256 above | This explains the sign but supplies neither a Lean expansion nor an all-small-$\varepsilon$ theorem. |
| Recursive series has compiled geometric coefficient bound and Volterra identity for $|A|\leq64$, $|B|\leq32$ | Proved; kernel-checked `coefficient_weighted_bound`, `solution_volterra`, `parameter_bounds` | The bound is used for the fixed certificate. |
| Generic geometric tail and degree-80 remainder are compiled | Proved; kernel-checked `geometric_coefficient_tail` and `short_remainder_lt` | The remainder is $2\cdot3^{16}/2^{81}<10^{-16}$. The delivered certificate controls the fixed pair; uniform extension beyond it is open. |
| Exact external checker encloses four shooting roots and returns a strict negative gap difference | Computed; pinned experiment command, exit 0, script SHA-256 above | The tested brackets and final interval are finite-scope computation; the Lean certificate independently proves the fixed result. |
| Four determinant roots connect to the first two binding min-max values | Proved; kernel-checked `first_shooting_root_is_minmax` and `second_shooting_root_is_minmax` | Root ordering is proved for the two tested potentials. |
| Under explicit continuity, spectrum and $c\geq0$ hypotheses, $V\mapsto V+c w$ shifts spectrum by $c$ and preserves the gap | Proved in prose | The quadratic form changes by $c b_w(u,u)$, so every trial-space upper bound changes by $c$, its greatest lower bound changes by $c$, and subtracting the first two values cancels $c$. The standalone Lean exploration is outside the target import path. |
| Extension to all sufficiently small positive slopes, robustness ranges, and an exact perturbative spectral-gap expansion | Open | No delivered declaration or computation closes these uniform claims. |
| Additional hypotheses such as symmetric weights, and whether a different ordinary constant potential minimizes under particular bounds | Open; literature reading | Lavine's unweighted theorem is prior literature and is not refuted by this weighted example. |
| Literal negation of the binding claim | Proved; kernel-checked `WeightedConvexPotentialRefutation.result` | The axiom closure is contained in `{propext, Classical.choice, Quot.sound}`. |

The supporting escape audit remains unfinished under [#27756](https://github.com/the-omega-institute/trureturing/issues/27756). The settling result is exempt under `basis=refutes`; all other newly published public declarations named in the issue remain pending the required CI `DTR-*` reading.

## ASSUMED-UNVERIFIED

Literature completeness is `ASSUMED-UNVERIFIED`. The perturbative all-small-slope extension, robustness ranges, exact perturbative expansion in Lean, symmetric-weight variants, and ordinary-constant minimizer variants remain open. The external computation is finite-scope evidence and does not replace the kernel-checked fixed certificate.
