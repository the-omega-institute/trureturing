---
slug: hsw17
bibkey: hemmerstraubwestrem2025riordan
doi: 10.37236/14401
url: https://arxiv.org/abs/2509.02796v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Partitions/HemmerStraubWestremWeightedAverage.result
---

# The weighted Ev character average

## Problem

Hemmer–Straub–Westrem, *New Identities in the Character Table of Symmetric Groups involving Riordan Numbers*, arXiv:2509.02796v1, Conjecture 6.1, equation (6.1), page 12 (journal Conjecture 17, page 15), states “For any integer $n\ge1$,” followed by

$$
\sum_{\lambda\vdash n}\frac{1}{z_\lambda}
 \sum_{\tau\in\operatorname{Ev}(\lambda)}\sum_{\mu\in\mathcal R_3(2n)}
 (-1)^{\ell(\tau)}\chi^\mu_\tau
=\sum_{\lambda\vdash n}\frac{1}{z_\lambda}
 \sum_{\tau\in\operatorname{Ev}(\lambda)}\chi^{(n,n)}_\tau
=\begin{cases}\binom{n/2+2}{2},& n\text{ even},\\0,&n\text{ odd}.\end{cases}
$$

Here $z_\lambda=\prod_{k\ge1}k^{m_k}m_k!$. Each occurrence of a part is independently doubled or replaced by two copies, with all resulting multiplicities retained. The preregistered formulation is [#21960](https://github.com/the-omega-institute/trureturing/issues/21960).

### Statement echo

| Source clause | Lean counterpart | Fidelity and boundary |
| --- | --- | --- |
| Every positive integer $n$ | `claim` quantifies all natural numbers with guard $1\le n$ | The zero term is excluded from the published assertion. |
| All partitions of $n$ and reciprocal $z_\lambda$ | `Nat.Partition n`, `weight`, existing `zPartition` | The existing multiplicity product is reused. |
| Every Ev replacement with multiplicity | Existing `evTypes lam.parts.toList` | Coincident cycle types remain repeated. |
| Even shapes with at most three rows and sign | Existing `R3 (2*n)`, sign by list length in `leftAverage` | Zero padding preserves the shapes. |
| Rectangular character | Existing `frobChar` at the padded triple $(n,n,0)$ in `rightAverage` | This is the binding Frobenius coefficient model. |
| Both equalities and even/odd value | `claim`, proved by `result` | Integer character sums are cast to rationals; integer division agrees with $n/2$ on the even branch. |

## Motivation

The pointwise identity `HemmerStraubWestrem.result` supplies the first equality after multiplication by the reciprocal centralizer factor and summation. The closed form evaluates the additional weighted sum uniformly in positive degree. The original private coefficient declarations `ev_right`, `right_coefficient` and `triProd` are reused through `Batteries.Tactic.OpenPrivate`, with no owner publication or second coefficient model.

## Gap

The proved proposition is exactly the binding coefficient-model formulation in #21960. The source identifies that model with ordinary irreducible characters through the classical Frobenius formula (Lemma 3.1). An internal partition-indexed Specht-module construction and a Lean equivalence to its trace character are not supplied. The ordinary-character interface described in `Problems/hemmer-straub-westrem-2025-weighted-ev-character-average.md` remains unresolved; no kernel proof of that interface is claimed.

## Route

For arbitrary part inputs $a_k$ in a commutative $\mathbb Q$-algebra, put $A_n=\sum_{\lambda\vdash n}z_\lambda^{-1}\prod_{k\in\lambda}a_k$. Removing one marked part gives

$$
nA_n=\sum_{k=1}^n a_k A_{n-k},\qquad A_0=1.
$$

The exact multiplicity identity is $z_{(k)\cup\lambda}=k(m_k+1)z_\lambda$. Coefficient induction proves uniqueness of the formal differential equation for $\sum_n A_nt^n$. For $a_k=2(z^k+1+z^{-k})$, this determines

$$
\sum_{n\ge0}A_nt^n=
(1-t)^{-2}(1-tz)^{-2}(1-t/z)^{-2}.
$$

The difference of adjacent Laurent coefficients, implemented by the constant term after multiplication by $1-z^{-1}$, cancels the factor $(1-t)^2$ and gives $(1-t^2)^{-3}$. Its coefficient at $t^{2m}$ is $\binom{m+2}{2}$ and every odd coefficient vanishes. These steps are private consumed helpers of the settling theorem, rather than additional public identities.

## Falsifier

A positive degree violating either equality under the binding definitions would contradict `result`. Finite tests alone establish no universal identity. A mismatch between the Frobenius coefficient model and a separately constructed representation would concern the unresolved interpretation bridge, which is outside this theorem's statement.

## Evidence

The settling declaration is `D5.S3.Combinatorics.Partitions.HemmerStraubWestremWeightedAverage.result`; the module is `D5/S3/Combinatorics/Partitions/HemmerStraubWestremWeightedAverage.lean`. Its admission basis is `open-problem-resolution (#21960; Proved)`, generality is G, and utility is none: the mathematical statements are unbounded symbolic identities. The axiom closure of every public declaration is contained in {propext, Classical.choice, Quot.sound}. Its proof-shape classification and the consumed helpers' classifications are bind-only; no escape witness or new general mathematical method is claimed.

The escape audit of the sole public theorem is unfinished: [#22528](https://github.com/the-omega-institute/trureturing/issues/22528). The guarded-equality template alone omits one conjunct; no faithful enrolled reconstruction and full variation/sensitivity evidence for both equalities is delivered. No Reg mirror or `declared_validated` registration is asserted.

The [independent checker](https://github.com/the-omega-institute/trureturing-experiments/tree/9286584dbd0ae1c3487b0899617c99df04b92bd2/docs/reports/hemmer-straub-westrem-conj17/) is `check.py` at commit `9286584dbd0ae1c3487b0899617c99df04b92bd2` of `the-omega-institute/trureturing-experiments`. Command: `python3 -I /tmp/op-hsw17/experiment-check.py`, using the byte-exact file extracted from that revision; exit 0. Script SHA-256: `4064101364694e4ba37605bd1758b308749badb95f3b523bc1ae06419643cf58`. Both weighted sums and the closed form agree on all 272 partitions for $0\le n\le12$, giving $1,0,3,0,6,0,10,0,15,0,21,0,28$. Independent rim-hook recursion compares 1003 distinct character pairs for $0\le n\le7$; an independent two-variable calculation checks every Ev type for $0\le n\le12$. These are finite computations.

## Triage

| Item | Status | Evidence kind and scope |
| --- | --- | --- |
| Repeated and mixed part sizes | proved | Kernel-checked private `z_partition_cons` gives exactly $k(m_k+1)$, and `cycle_average_recursion` sums all partitions without a distinct-part condition. |
| Arbitrary part inputs in a commutative $\mathbb Q$-algebra | proved | Kernel-checked private `cycle_average_recursion`, `cycle_average_derivative` and `power_series_ode_unique` retain that coefficient-ring scope. |
| Target generating series and all positive degrees | proved | Kernel-checked private `weighted_constant_term_series`, `coefficient_even_cube`, `rightAverage_closed`, and public `result` give $(1-t^2)^{-3}$, parity and the even binomial value. |
| Bookkeeping value at zero | computed | The pinned independent checker above returns 1 at $n=0$, exit 0; `claim` remains restricted to $n\ge1$. |
| Other row bounds or arbitrary replacements of the factor 2 | open | No analogous closed form is asserted. |
| Source identities for $N\ge2$, separate all-$N$ q-series assertion, bijective questions | open | No theorem in this delivery settles those questions. |
| Internal Specht-module equivalence for the inherited coefficient model | open | No compiled representation-theoretic bridge is supplied; the binding proposition uses the inherited coefficient model. |

### What the settlement shows

The cancellation mechanism is coefficientwise: centralizer multiplicities give the recurrence, formal ODE uniqueness identifies its solution, and adjacent-coefficient subtraction produces an even series with quadratic binomial coefficients. Repeated part sizes require no additional hypothesis. The recurrence and uniqueness helpers apply to any commutative $\mathbb Q$-algebra, while the final closed form uses the specified Laurent input. The source's higher-row and bijective questions remain open here. No downstream source theorem is claimed to depend on this newly proved coefficient-model evaluation.

The literature screen in #21960 distinguishes the pointwise sibling identity and degree/knapsack/bijection follow-ups from the weighted closed form. It records no settlement in the screened scope. Literature completeness is `ASSUMED-UNVERIFIED`.

## ASSUMED-UNVERIFIED

The literature search is not exhaustive: citation-index rate limits, the unread full dissertation, and unexhausted broad queries remain as recorded in #21960. The classical representation-theoretic interpretation is a literature input, not a kernel-checked equivalence here. Finite checker results do not extend beyond their stated ranges. Escape registration remains unfinished under #22528.
