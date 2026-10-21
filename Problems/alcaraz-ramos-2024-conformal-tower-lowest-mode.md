---
slug: alcaraz-ramos-2024-conformal-tower-lowest-mode
bibkey: alcarazramos2024conformaltower
doi: 10.1103/PhysRevE.109.044138
url: https://arxiv.org/abs/2402.09936v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/SpinChains/AlcarazRamosConformalTowerRefutation.result
---

# The Alcaraz–Ramos lowest-mode conformal prediction fails

## Problem

F. C. Alcaraz and L. M. Ramos, *Conformally invariant free parafermionic quantum chains with multispin interactions*, arXiv:2402.09936v3, Physical Review E 109, 044138, propose the leading prediction
$M\varepsilon_i\to\pi A^{(N)}(x_s^{(N)}+i-1)$ for each fixed $i\ge1$.
Their conjectured constants for $N=3$ and $M\equiv0\pmod3$ are $A^{(3)}=2\sqrt3$ and $x_s^{(3)}=7/6$.
The prediction is **Refuted** for homogeneous couplings, already at $i=1$ along $M=3m$.
[Preregistration #19220](https://github.com/the-omega-institute/trureturing/issues/19220) fixes the source and Lean conventions; its corrected scaled constant is $7\pi/(3\sqrt3)$.
The [Library note](../Library/QuantumContext/alcarazramos2024conformaltower.md) gives the source quotations and locators. Printed Eqs. (26)–(27), (38), (39), (41) correspond to TeX labels (3.11)–(3.12), (4.7), (4.8), (4.10).

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| $P_M=P_{M-1}-z\lambda_M^N P_{M-N}$, with $P_M=1$ for $M\le0$ | `poly`, specialized to $N=3$, $\lambda_j=1$, with index shift $\operatorname{poly}(n)=P_{n-2}$ | All three initial values and the recurrence are literal |
| $P_M$ for nonnegative $M$ | `P M = poly (M+2)` | Natural-index representation of the source recurrence |
| $\varepsilon_i=1/z_i^{1/N}$ over the positive roots | `quasienergy M i`: roots with multiplicity, positive-root filter, decreasing root order, real exponent $-1/3$ | Increasing quasienergy order; index $i-1$ uses truncated natural subtraction |
| Every fixed $i\ge1$ | `claim`: every natural `i` with `1 ≤ i` | No mode is dropped from the conjecture |
| Leading behaviour with $A^{(3)}=2\sqrt3$, $x_s^{(3)}=7/6$ | `claim`: `Tendsto` of $3m\varepsilon_i(3m)$ to $\pi(2\sqrt3)(7/6+i-1)$ | The product $3m$ is natural before the real cast; $i$ is cast to real |
| $M\equiv0\pmod3$ | The sequence $M=3m$ | Exact nonnegative residue class |
| Refutation | `result : ¬ claim` | The contradiction uses $i=1$ only |

Absent root indices are assigned zero in `quasienergy`, as fixed by the binding conventions. A positive proposed limit forces the selected quasienergy to be positive eventually; the proof then obtains an actual positive root. This totalization adds no hypothesis to the claim and supplies no spurious counterexample at absent indices.
Every binder and conjunct implements a row above; no source clause is weakened or dropped.

## Motivation

The prediction assigns a conformal arithmetic progression to every fixed low mode. A nonzero discrepancy at the first mode distinguishes that assertion from a possible asymptotic spacing law at large mode index.

## Gap

The source reports agreement of numerical roots with the conjectured exact constants. This module disproves the fixed-index prediction. It does not prove existence or identify the value of the actual limiting lowest quasienergy.

## Route

The module is `D5/S3/Quantum/SpinChains/AlcarazRamosConformalTowerRefutation.lean`; all names below belong to its namespace.
Private `poly_coeff` proves the recurrence coefficient formula $(-1)^j\binom{n-2j}{j}$ by induction. `P_closed` and `P_eval_closed` give the finite expansion. Reversing its indices yields `scaling_identity`, relating a positive-root quasienergy to
$Q_m(u)=\sum_{k=0}^m(-1)^ku^{3k}\binom{m+2+2k}{3k+2}/m^{3k+2}$.

Private `shifted_choose_limit` uses Mathlib's `isEquivalent_choose` and `tendsto_add_mul_div_add_mul_atTop_nhds`. The summable majorant and Mathlib's `tendsto_tsum_of_dominated_convergence` give `Q_moving_limit`: if $v_m\to u$ and eventually $|v_m|\le5$, then $Q_m(v_m)\to F(u)$, where
$F(u)=\sum_{k\ge0}(-1)^ku^{3k}/(3k+2)!$.
The alternating-series lower bound in `six_terms_lower`, followed by rational endpoint estimates in `interval_series_positive`, gives $F(u)>0$ on $[4.2321,4.2323]$. `predicted_interval` places $7\pi/(3\sqrt3)$ there using `Real.pi_gt_d6`, `Real.pi_lt_d6`, and square-root bounds. Under `claim`, the $i=1$ positive roots would instead force this series value to be zero. `result` contradicts its strict positivity.

The module imports only pinned Mathlib and has no frozen D5 prerequisite. Its admission basis is `open-problem-resolution (#19220; Refuted)`. The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

## Falsifier

A mismatch in the recurrence, root ordering, real power, residue class, or fixed-index limit would prevent this theorem from refuting the source's prediction. The statement echo fixes those choices. The final theorem is the exact negation of the binding `claim`, without an assumption that an actual limiting zero exists.

## Evidence

**Kernel-checked:** `D5.S3.Quantum.SpinChains.AlcarazRamosConformalTowerRefutation.result` and its private proof dependencies named in Route. The axiom closure of every public declaration is contained in {propext, Classical.choice, Quot.sound}. The sequential convergence and interval positivity statements are private theorems; no public theorem about existence of the actual limit is asserted.

**Computed:** [the pinned experiment](https://github.com/the-omega-institute/trureturing-experiments/tree/e318d5e6cb8bfc5e04e76b76b58bf02729859b9b/docs/reports/alcaraz-ramos-2024-conformal-tower-lowest-mode). Command: `python3 check.py` in that directory, exit 0 (`RESULT PASS`); `check.py` SHA-256: `a2622ee170d7437ca3f729ff25e79e29a992b43f40d64ce07228303a64e3487c`. The script uses 60-digit mpmath arithmetic. Its exact tested scope is:

- The closed expression $[e^{-u}+2e^{u/2}\cos(\sqrt3u/2-2\pi/3)]/(3u^2)$ agrees numerically with the series at $u=0.7,3.1,9.4$, with maximum error $5.06\times10^{-61}$.
- At $m=50,200,800,3200$, a bisection in $[3.9,4.6]$ gives $3u_1(m)=12.2067818314,12.5718933829,12.6673905808,12.6915448671$. The recurrence changes sign at the corresponding transformed points. These four readings increase; Richardson extrapolation gives $12.6995963$.
- Scanning the positive axis from $0.5$ in steps of $0.01$ locates the first three sign changes of the displayed function. Its first computed zero gives $3u_1(F)=12.6996215773$, a gap $0.00302603$ from $7\pi/\sqrt3$. The ratio $3u_1(F)/(2\sqrt3\pi)=1.166944723$ agrees within $10^{-6}$ with Table I's $1.1669439$.
- The first two computed zero spacings are $3.62658567491$ and $3.6276031251$, and are unequal at the tested precision.

These numerical checks neither certify that no earlier zero was missed nor establish a uniformly convergent sequence of first roots, an exact actual limit, or an asymptotic large-index spacing law.

## Triage

### What the settlement shows

1. **Kernel-checked — settlement.** `result` disproves the exact prediction encoded by `claim`, using $i=1$ only. The failure is that the predicted scaled root $7\pi/(3\sqrt3)$ lies in an interval where the limiting series is strictly positive, while the root equation and the assumed prediction would make its value zero.

2. **Kernel-checked — sequential convergence.** Private `Q_moving_limit` proves $Q_m(v_m)\to F(u)$ whenever $v_m\to u$ and eventually $|v_m|\le5$. This is the sequential statement, not a separately stated uniform-on-compacta theorem.

3. **Kernel-checked — positive interval.** Private `interval_series_positive` proves $F(u)>0$ for every $u\in[4.2321,4.2323]$; private `predicted_interval` puts $7\pi/(3\sqrt3)$ in that interval. These are the positivity and localization used by `result`.

4. **Computed — discrepancy and finite checks.** The experiment in Evidence gives $3u_1(F)=12.6996215773$, discrepancy $0.00302603$, the four finite-size sign-change checks, and the comparison with Table I. Those exact decimal readings are computed, not exact values established by Lean.

5. **Open here — actual limit and extensions.** Existence and the exact value of the actual lowest-mode limit, the claim that no three positive zeros of $F$ form an arithmetic progression, other $N$ and residue classes, and asymptotic large-index spacing are not proved here. The first-three-zero computation is finite numerical evidence only. The closed exponential-cosine expression suggests a decaying-term displacement of the first roots; this interpretation and the survival of $A^{(3)}=2\sqrt3$ as an asymptotic spacing are not kernel-checked conclusions of this module. The universal conformal prediction cannot support deductions that require it; independently proved source results retain their own hypotheses and scope.

6. **Literature reading.** The screen recorded in #19220 covers source versions v1–v3; later author works arXiv:2512.08011, 2606.13265, 2511.13978, 2507.02623; reachable citing works 2506.07151, 2509.16309; and antecedents 2005.14622, 2010.01116, 2108.04372, 2109.01938. It reports no settlement in that searched scope. This is the preregistration's attributed literature reading; completeness is `ASSUMED-UNVERIFIED`.

## ASSUMED-UNVERIFIED

Literature completeness and priority are `ASSUMED-UNVERIFIED`. The decimal values and finite-size observations are computations at the stated precision and tested inputs. They do not extend the kernel-checked refutation to a proof of the actual limit, an arithmetic-progression classification, other parameters, or a large-index spacing theorem.
