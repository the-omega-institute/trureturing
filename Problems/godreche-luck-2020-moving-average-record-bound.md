---
slug: godreche-luck-2020-moving-average-record-bound
bibkey: godrecheluck2020records
doi: 10.1088/1742-5468/ab5d08
url: https://arxiv.org/abs/1907.07598
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/Records/MovingAverageRecordBound.result
---

# Godrèche–Luck moving-average record bound

## Problem

C. Godrèche and J.-M. Luck, *Records for the moving average of a time series*, arXiv:1907.07598v2, J. Stat. Mech. (2020) 023201, DOI 10.1088/1742-5468/ab5d08, state after equation (6.33) that the data suggest $3/(2n)$ is an absolute upper bound for the record probability $Q_n$.

### Statement echo

The source's two-term moving average is $Y_n=X_{n-1}+X_n$, with records counted from the first complete sum $Y_2$. The formal `recordProb` event is the strict comparison $Y_n>\max(Y_2,\ldots,Y_{n-1})$ in the preregistered zero-based coordinates. The theorem `movingAverage_record_bound` proves the bound for every atomless probability measure on $\mathbb R$ and every $n\ge3$; `result` specializes it to the density-form `claim`. Its `Continuous f` hypothesis is the density restriction fixed by preregistration [#15864](https://github.com/the-omega-institute/trureturing/issues/15864); discontinuous densities in the paper are covered by the public atomless theorem.

## Motivation

The source presents the inequality as a data-supported absolute upper bound. The delivered result proves that bound for all atomless laws, which includes every density law in the source's setting.

## Gap

Before this settlement the source's statement was supported by the exponentially broad limit and numerical data. The formal gap was a uniform proof for arbitrary atomless laws.

## Route

For $n\ge3$, write the cyclic edge sums as $C_i=X_i+X_{i+1}$, with indices modulo $n$. Atomlessness makes every equality $C_i=C_j$ a null event because a coordinate appears with coefficient $1$ or $-1$ in the difference. Rotation preserves the iid product measure and makes each unique cyclic maximum have probability $1/n$. Outside the null tie set, the record event is the union of the maximum-at-the-terminal-edge event and the event that the terminal edge is the runner-up while the next cyclic edge is maximal. Reversal preserves the product law, fixes the maximal edge, and pairs the latter event with a disjoint runner-up event. Thus the second contribution is at most $1/(2n)$ and the total is at most $3/(2n)$.

### Encoding conventions

Finite-index bounds use `i.isLt` before `omega`. The public `NoAtoms` hypothesis is installed internally as `NullSingletonClass`; these are the deprecated alias and its current owner. Reversal uses `MeasurableEquiv.piCongrLeft` with `Fin.revPerm`. These choices preserve the literal preregistered event and its coordinate bounds.

## Falsifier

A probability law with no atoms and some $n\ge3$ for which the strict record probability exceeds $3/(2n)$ would falsify the settling theorem. Such a witness would have to invalidate one of the null-tie, rotation, or reversal steps.

## Evidence

The kernel-checked evidence is `D5/S3/StatisticalMechanics/Records/MovingAverageRecordBound.movingAverage_record_bound`, together with the settling declaration `D5/S3/StatisticalMechanics/Records/MovingAverageRecordBound.result`. The axiom closure is contained in `{propext, Classical.choice, Quot.sound}`. The module's public result has admission basis `open-problem-resolution (#15864; Proved)` and `utility: none`.

The experiment entry [`docs/reports/godreche-luck-2020-moving-average-record-bound/check.py`](https://github.com/the-omega-institute/trureturing-experiments/tree/c8fd3bf1152cab522897dca197f2203a35294d59/docs/reports/godreche-luck-2020-moving-average-record-bound) is pinned to commit `c8fd3bf1152cab522897dca197f2203a35294d59`. Command: `python3 check.py`; exit 0. Script SHA-256: `356f179d7742b5fac1cdf3cc23449818dda7d820a6da27e19681a8aab9d51de2`.

The deterministic part checks the oriented-path counting identity behind $2nQ_n=2+\Pr(\text{the two largest cyclic sums are adjacent})$ on 21,000 random integer configurations with distinct cyclic sums, for $n=3,\ldots,9$, with zero mismatches. The probabilistic checks use seed 20191106 and 400,000 samples per law and length: exponential, uniform, lognormal, Pareto-index-$1/2$, and half-Cauchy laws for $n=3,\ldots,12$. Their bound and identity tolerance checks report `bad=0`; the samples do not establish an exact probability or an unbounded limiting statement.

For general windows the script samples $p=3$, $n=3,\ldots,12$, and $p=4$, $n=4,\ldots,13$, under exponential, Pareto-index-$1/2$, and half-Cauchy laws, again with 400,000 samples per case. The exponential readings of $nQ_n^{(p)}$ are $(3.000,1.999)$ at $p=3$, $n=3,4$, against $R_3=1.8750$, and $(4.000,2.501,2.245)$ at $p=4$, $n=4,5,6$, against $R_4=2.1875$. This exploration prints values without an assertion for the general-window inequality.

## Triage

| Item | Status | Evidence kind and boundary |
| --- | --- | --- |
| Null-tie, rotation, and reversal mechanism | proved | Kernel-checked by `movingAverage_record_bound` and its private helpers: pairwise cyclic ties are null; rotation gives the maximum contribution $1/n$; reversal bounds the runner-up contribution by $1/(2n)$. |
| Exact identity $2nQ_n=2+\Pr(\text{top two adjacent})$ | computed | The experiment checks the deterministic counting identity on 21,000 configurations, $n=3,\ldots,9$, and its probabilistic form within the stated Monte Carlo tolerances; no kernel theorem for this identity is claimed. Conditional on the exact identity, equality in the bound is equivalent to almost-sure adjacency. |
| Tightness at $n=3,4$ | proved in prose | The source's universal values $Q_3=1/2$ and $Q_4=3/8$ (Section 2.6) give $nQ_n=3/2$ directly. This equality is not stated by a Lean theorem in this delivery. |
| Exponentially broad limiting value | literature result | Equation (6.33) gives the source's limit $Q_n=3/(2n)$ for each $n\ge3$ as the breadth parameter tends to infinity. The experiment has no breadth-parameter sweep. |
| General-window assertion for $p\ge3$, $p\le n\le2p-2$ | proved in prose | Section 7.1 supplies the universal values; the derivation below shows that they exceed $R_p/n$ throughout this range. No general-window Lean theorem is delivered. |
| General-window finite samples | computed | The experiment scopes and readings are those listed in Evidence; they agree with the short-window obstruction and do not prove a uniform bound. |
| Corrected general-window range $n\ge2p-1$ | open | No theorem in this delivery settles this range for $p\ge3$. |
| Typeset journal wording | open | The arXiv v2 text is the checked source; the typeset journal text remains `ASSUMED-UNVERIFIED`. |

### What the settlement shows

**Kernel-checked:** `movingAverage_record_bound` settles the published two-term upper-bound question for every atomless probability law. Continuity, positive support, and the existence of a density are unnecessary for that theorem; `result` retains the preregistered density statement. The decisive estimate is the disjoint reversal pairing within a cyclic maximum event of mass $1/n$.

**Computed:** the counting identity identifies adjacency of the top two cyclic sums as the extra contribution above $1/n$ on the tested configurations. If the exact probabilistic identity holds, then $Q_n=3/(2n)$ exactly when that adjacency event has probability one. This equivalence is algebraic explanation conditional on the identity, not a separate kernel-checked result.

**Proved in prose from the source's universal values:** write $n=p+k$ and $P_k=\binom{2k}{k}/4^k$. Equation (7.4) gives $Q_{p+k}^{(p)}=P_k$ for $0\le k\le p$, including $P_0=1$; (7.10) gives $R_p=(2p-1)P_{p-1}$. For $F_k=(p+k)P_k$,

$$
\frac{F_{k+1}}{F_k}=\frac{(p+k+1)(2k+1)}{(p+k)(2k+2)}<1\qquad(0\le k\le p-2),
$$

because the denominator minus numerator is $p-k-1>0$. Hence $F_k>F_{p-1}=R_p$ throughout $0\le k\le p-2$. The all-$n\ge p$ general-window assertion therefore fails for every $p\ge3$ in $p\le n\le2p-2$, already with $Q_p^{(p)}=1$. The surviving candidate is the bound for $n\ge2p-1$, consistent with the source's overlap values at $n=2p-1,2p$.

**Open:** the corrected general-window bound for arbitrary atomless laws and $p\ge3$ needs additional work. The source's distribution-specific asymptotic formulas and its exponentially broad limit are outside the kernel-checked result; proving the two-term upper bound imposes no revision of those formulas.

## ASSUMED-UNVERIFIED

The typeset journal wording has not been independently read; the arXiv v2 source and its PDF are the verified literature texts. The general-window extension for $n\ge2p-1$ is an open mathematical question. The escape audit for the positive declarations `movingAverage_record_bound` and `result` is unfinished under issue [#16029](https://github.com/the-omega-institute/trureturing/issues/16029); the scoped DTR rule reports `DTR-Unregistered` for each target. The missing evidence comprises a lawful complete source selection, whole-family variation, operand sensitivity, and actual observational dependence; no Reg source is retained.
