---
slug: balaper-a281184-phi2period
bibkey: bala2026totientsquareperiod
doi: null
url: https://oeis.org/A281184
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Periodic/BalaA281184TotientSquarePeriod
---

# Bala's A281184 totient-square period

## Problem

Peter Bala's unpaginated OEIS A281184 conjecture states:

> E.g.f. C(x)^3 = d/dx log(C(x) + S(x)), where C(x) and S(x) are described by A281181 and A281180, respectively. Conjecture: the sequence {a(n)} taken modulo a positive integer k is eventually periodic with the period dividing phi(k)^2, where phi(n) = A000010(n). An example is given below. - _Peter Bala_, Feb 16 2026

### Statement echo

| source clause | Lean counterpart | fidelity |
| --- | --- | --- |
| Positive integer modulus | `k : ℕ`, hypothesis `1 ≤ k` | exact |
| Eventual period dividing $\varphi(k)^2$ | Tail congruence with shift `(Nat.totient k)^2` | exact: the prescribed shift is a period |
| Integer sequence given by source EGF | Existential `a : ℕ → ℤ` and the factorial-scaled `eCoeff` identity | exact |
| Source defining equation | Rational series witnesses and the literal equation in `claim` | exact |
| Formal integration constant | Zero constant coefficient for the primitive | explicit source convention |
| Even EGF indexing | Degree `2*n`, for every natural `n` | exact |
| Related $S$ and logarithmic derivative | Zero initial $S$, quartic ODE, and derivative of `PowerSeries.logOf (C + S)` | exact |

The dropped-or-weakened clause set is empty. The source's zero-constant primitive and factorial-scaled coefficient conventions appear literally in the claim. Proofs consume the existing EGF and primitive owners. Extra existential series and integer witnesses supply existence and integrality, rather than assume them.

## Motivation

The prescribed shift $\varphi(k)^2$ gives a uniform arithmetic period bound for every positive modulus. The claim includes the original generating-series specification and the integer sequence that it defines.

## Gap

The OEIS source states a conjecture. This module proves the exact binding proposition over rational formal series. Literature completeness and historical priority remain `ASSUMED-UNVERIFIED`.

## Route

Integral derivation flows realize the source equations. Truncated polynomial operators give prime-power annihilators and tail periods. The proof combines prime-power congruences into the prescribed all-moduli shift, and supplies the rational series and integer coefficient witnesses.

## Falsifier

A source-defined integer sequence and positive modulus with no tail invariant under the shift $\varphi(k)^2$ would refute the assertion. Finite agreement alone would not establish it.

## Evidence

Kernel-checked statement: `D5.S1.Recurrence.Periodic.BalaA281184TotientSquarePeriod.result`, of type `D5.S1.Recurrence.Periodic.BalaA281184TotientSquarePeriod.claim`. The formalization is in `D5/S1/Recurrence/Periodic/BalaA281184TotientSquarePeriod.lean`; its Blueprint displays the complete proposition. The module has `generality: I`, `utility: none`, and `admission_basis: open-problem-resolution (#21643; Proved)`.

The four-slot escape audit is unfinished: [issue #21972](https://github.com/the-omega-institute/trureturing/issues/21972) names the public targets and the missing faithful realization, readout, variation and sensitivity evidence. No validated registration is asserted.

## Triage

`theorem`.

### What the settlement shows

- **Proved, kernel-checked:** all five exact claims include rational source-series existence and integer EGF witnesses. The declarations are `BalaA281180TotientSquarePeriod.result`, `BalaA281181TotientSquarePeriod.result`, `BalaA281183TotientSquarePeriod.result`, `BalaA281184TotientSquarePeriod.result` and `BalaA281440TotientSquarePeriod.result`, under `D5.S1.Recurrence.Periodic`.
- **Proved, kernel-checked:** for every $P\in\mathbb Z[X]$ with $P(0)=1$, every integral polynomial observable, prime $p$ and positive $r$, the derivative-index shift $\varphi(p^r)^2$ is a period modulo $p^r$ after index $p^{2r-1}$. This is `AutonomousDerivationTotientSquarePeriod.BalaTruncated.prime_power_derivative_period` with its parameter $s=r-1$.
- **Proved, kernel-checked:** odd-prime branches work for every $q=2h+1$ (`BalaA281181TotientSquarePeriod.BalaOddBranch.source_derivative_period_odd`, a private theorem). The complete all-moduli source-period theorem covers $q=3$ or $q=7$ and every nonnegative observable exponent (`BalaA281181TotientSquarePeriod.BalaPolynomialSystem.even_sequence_period`).
- **Proved, kernel-checked:** every integral polynomial operator $a\partial^2+b\partial$ with $b(0)=1$ has the stated period at powers of $2$ (`BalaA281181TotientSquarePeriod.BalaSecondOrderMatrix.two_power_period`, a private theorem).
- **Computed:** the experiment below checks exactly 120,000 comparisons across the five members, moduli $1\le k\le60$, and 400 consecutive comparisons per member and modulus, starting at the checker's recorded onset. Its exit code is $0$ and final marker is `ALL_CHECKS_OK`. These finite comparisons establish no uniform extension.
- **Open:** sharp onsets, least eventual periods, and complete $q=5$ or larger odd-$q$ extensions beyond the implemented $q=3,7$ cases are not formalized.

The decisive mechanism is a characteristic-$p$ restricted-derivation relation on truncated polynomial rings. It yields an operator annihilator, lifts through prime powers, and combines the prescribed periods by divisibility of totients. Odd-prime square-root coordinates and a second-order operator at $2$ connect the hyperbolic source equations to this argument. These mechanisms are kernel-checked by the declarations named above; the exposition asserts no additional theorem.

The periodicity conclusions for the five source sequences are unconditional within the stated formal-series conventions. Source existence and integrality are included in each `claim`; no asymptotic, least-period or analytic-convergence conclusion is asserted.

### Experiment

[Exact checker and output](https://github.com/the-omega-institute/trureturing-experiments/tree/40a03f8dee635181bd023fbb3c3f77c0a633f408/docs/reports/bala-phi2-period).
Command: `python3 docs/reports/bala-phi2-period/check.py`, run from the experiments repository; exit $0$. Script SHA-256: `1d89e342f50756810d8a9fef2202e23650a6748b84eda6684bd4ec6c355ec816`. The script bytes agree with the pinned commit. The tested scope and result are the computed item above.

## ASSUMED-UNVERIFIED

Literature completeness is `ASSUMED-UNVERIFIED`. The preregistration #21643 records the source and literature checks. Integral-logarithmic-coordinate period theorems do not directly apply to the source EGFs, whose required logarithmic weights are nonintegral. Carlitz's *Kummer Congruences and the Schur Derivative* (DOI `10.2307/2372544`) has not been read in full.

The preregistrations #21640–#21644 were filed on 2026-10-25. Published on 2026-10-31, Lien-Hung Su's *Quadratic Derivations and Uniform Modular Periods for Six Inverse-Function Sequences*, [Zenodo record 23835577](https://zenodo.org/records/23835577) (DOI `10.5281/zenodo.23835577`), is a later independent settlement and states proofs of A281180, A281181, A281183, A281440 and A281428. The preregistration's literature reading covers its abstract only; manuscript correctness is `ASSUMED-UNVERIFIED`. No claim of mathematical priority or exhaustive literature clearance is made.
