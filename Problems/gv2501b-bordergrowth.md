---
slug: gv2501b-bordergrowth
bibkey: grauollermarcenvarona2022delannoy
doi: 10.48550/arXiv.2501.09726
url: https://arxiv.org/abs/2501.09726v2
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Delannoy/GrauOllerMarcenVaronaPowerBorderGrowth.result
---

## Problem

Grau, Oller-Marcén and Varona, *A class of weighted Delannoy numbers*, arXiv:2501.09726v2, Section 6, arXiv page 18, conjecture the additive-error diagonal-ratio limit for the border b(n)=n^n (OEIS A346385). The preregistration is [#19939](https://github.com/the-omega-institute/trureturing/issues/19939); the [companion dossier](gv2501a-bordergrowth.md) treats the other border. The source is recorded in [the Library note](../Library/Asymptotics/grauollermarcenvarona2022delannoy.md).

For m,n≥0 the array has identical borders f(n,0)=f(0,n)=b(n) and interior recurrence f(m+1,n+1)=f(m,n+1)+f(m+1,n)+f(m,n). Both selected borders have b(0)=1; the power convention includes 0^0=1. The asserted real limit is

$$\frac{f(n+1,n+1)}{f(n,n)}-e(n+1/2)\longrightarrow0.$$

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| α=β=γ=1 and prescribed identical borders | Factorial module `f` | The two boundary cases and all three interior summands are literal. |
| b(n)=n^n | `claimPower` | Natural self-power; no asymptotic substitute for the border. |
| Source notation a_n≈b_n means a_n−b_n→0 | `claimPower` and `result` | Convergence of the real difference to zero along all natural indices. |
| Diagonal ratio and source shift | `claimPower` | Both entries cast to ℝ before division; the successor and shift are unchanged. |
| No additional source hypothesis | Closed `result` | No eventual-positivity, convergence or expansion premise is imposed on the conjecture. |

The auxiliary definitions delta, conv, Q, G and P are repository constructions, not additional external source assertions. The exponential coefficients are existing Mathlib expressions, used directly. Their full bodies are displayed in the factorial Blueprint. The unit-border recurrence is related privately to the existing `SpeyerUniformNormality.qAB` evaluated at one.

## Motivation

The settling declaration is `D5.S3.Combinatorics.Delannoy.GrauOllerMarcenVaronaPowerBorderGrowth.result`, with `generality: I`, `utility: none` and `admission_basis: open-problem-resolution (#19939; Proved)`. The family consists of this module and the companion module, with full namespaces `D5.S3.Combinatorics.Delannoy.GrauOllerMarcenVaronaFactorialBorderGrowth` and `D5.S3.Combinatorics.Delannoy.GrauOllerMarcenVaronaPowerBorderGrowth`. There is no atom or coverage claim.

## Gap

A leading multiplicative asymptotic alone does not establish a vanishing additive error in a ratio growing linearly with n. The required bridge controls the normalized diagonal to first order and transfers that control through the consecutive-index ratio.

## Route

The exact border convolution expresses each diagonal entry through border increments and unit-border Delannoy values. The private d_eq_binomial theorem identifies the unit-border array with the existing polynomial qAB evaluated at one; qAB_pos supplies positivity. Factorial majorants dominate the normalized kernel and its first-order error uniformly in n. Fixed-index limits and dominated convergence then give a first-order normalized-diagonal expansion. For the power border, finite products of consecutive border ratios preserve this expansion; the logarithm remainder bound and differentiability of exp supply the input. Reciprocal-ratio algebra and the shared ratio-transfer theorem yield the two source shifts.

## Falsifier

A failure of the stated real difference to converge to zero for the literal recurrence and selected border would refute this claim. A finite discrepancy would instead require checking the definitions and arithmetic; finite evidence alone does not establish convergence or its failure.

## Evidence

The Lean source is [PowerBorderGrowth](../D5/S3/Combinatorics/Delannoy/GrauOllerMarcenVaronaPowerBorderGrowth.lean), with its Scribe and emitted Blueprint at the matching address. Its result has the full proposition displayed in the Blueprint. The family also publishes the unchanged existing owner `SpeyerUniformNormality.qAB` and `qAB_pos` for reuse.

The four-slot escape audit for all new public theorems and the published owner declarations is unfinished in [#22168](https://github.com/the-omega-institute/trureturing/issues/22168). The missing source reconstruction, realization bridge, whole-family variation/sensitivity and observational-dependence evidence is separate from the kernel proof. No validated registration is asserted.

### Finite experiment

The independent checker is [the pinned experiment](https://github.com/the-omega-institute/trureturing-experiments/tree/865efe58aacf453e1ac30ff2afe058e5a97cbb64/docs/reports/grau-oller-marcen-varona-2022-weighted-delannoy-border-growth). Its `check.py` has SHA-256 `7d52312b369cd77b6871b5673d5c280423447d55cb71196421282ad2ced51e21`. Running Python 3.14 on the exact Git blob at that revision exits 0. The executed command is `git -C /Users/auric/trureturing-experiments show 865efe58aacf453e1ac30ff2afe058e5a97cbb64:docs/reports/grau-oller-marcen-varona-2022-weighted-delannoy-border-growth/check.py | python3` (with shell pipefail). The factorial error at n=400 is −5.101948e−03; the power error at n=300 is −6.225838e−03. The first eight factorial diagonal values are 1, 3, 15, 85, 511, 3221, 21339, 149969; the first six power values are 1, 3, 19, 151, 1439, 16651. The check also finds decreasing factorial absolute errors for 50≤n<400. These are finite computations, separate from the unbounded theorems.

## Triage

### What the settlement shows

| Item | Status | Evidence kind and scope |
| --- | --- | --- |
| Both additive-error conjectures | proved | Kernel-checked `FactorialBorderGrowth.result` and `PowerBorderGrowth.result`, in the full namespaces named in Motivation. |
| Exact border convolution, global factorial majorants, fixed-index first-order limits, dominated convergence and first-order ratio transfer | proved | Kernel-checked factorial `border_convolution`, `Q_scaled_bound`, `Q_scaled_limit`, `factorial_first_order` and `ratio_transfer`; power `U_tsum_limit` and `border_first_order`. |
| General first-order normalized-diagonal theorem for nonzero natural borders satisfying the A bounds and scaled convergence | proved | Kernel-checked private power `border_first_order`; it assumes every b(n)≠0, 0≤A_n≤1, 0≤ρ≤1, and first-order scaled convergence. It requires no b(0)=1 assumption. |
| First-order n^n input and the half-shift | proved | Kernel-checked private power `L_error`, `L_scaled_limit`, `exp_scaled_limit`, `A_power_scaled_limit` and `border_power_limit`; the proof uses the pinned logarithm remainder and derivative of exp, then reciprocal-ratio algebra. |
| Factorial error at n=400 and power error at n=300 | computed | Pinned finite checker in Evidence, exit 0 and the stated SHA-256. |
| Stronger O(n⁻²) expansion, explicit constant evaluations and explicit ratio rates in the issue outline | open | No delivered declaration states these stronger conclusions. |
| Borders violating A_n≤1, unequal borders, arbitrary α/β/γ, higher-order expansions and exhaustive literature coverage | open | Outside the assumptions and conclusions proved here. |

The decisive mechanism is a first-order expansion under a common summable majorant, applied to an exact convolution. A second-order expansion is unnecessary for these additive-error ratio limits. The general private theorem covers other positive natural borders when its precise A bounds and first-order convergence hold; this is a conditional extension, not a classification of all such borders. The two conjectural statements in the source become theorems. No change to any other result of the source is asserted.

### Literature status

The bounded literature screen recorded in #19938 and #19939 found no settlement of these exact additive-error limits. The source arXiv v2 Section 6 explicitly labels both as conjectures. The screen distinguishes ordinary weighted-Delannoy zeros and normal limits (Chen–Zhang–Pan), lattice aggregation (Rozhkovskaya), uniform ordinary-Delannoy estimates (Kosz–Niksiński–Wróbel) and the Delannoy path lattice (Chen–Dong) from superexponential boundary data. It does not audit all cited literature in full. Literature completeness is `ASSUMED-UNVERIFIED`.

## ASSUMED-UNVERIFIED

The bounded literature screen establishes no exhaustive completeness or priority claim. The neighbouring open questions in Triage remain open. The experiment has only the finite scope stated in Evidence. The unfinished four-slot audit is tracked separately in #22168.
