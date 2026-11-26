---
slug: ide-konno-mano-2026-hypercube-walk-limit-coincidence
bibkey: ide2026scaling
doi: 10.48550/arXiv.2611.31635
url: https://arxiv.org/abs/2611.31635v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Dynamics/SymmetricHypercubeWalk/Criterion.common_shell_weakLimit_iff_gap
  - D5/S3/Quantum/Dynamics/SymmetricHypercubeWalk/Criterion.exists_common_shell_weakLimit_iff
---

# Ide–Konno–Mano coincidence of symmetric hypercube walk limits

## Problem

Yusuke Ide, Norio Konno and Shuhei Mano, *Scaling Limits of Time-averaged
Distributions for Symmetric Quantum Walks on Hypercubes*, arXiv:2611.31635v1,
§5 “Discussion,” printed p. 14, final paragraph before Acknowledgements.
[Versioned PDF](https://arxiv.org/pdf/2611.31635v1#page=14)

> It is therefore an open problem to find a necessary and sufficient condition for the coincidence of the scaling limits.

For each dimension $d$, take shell weights $w_d(h)$ that are nonnegative
for $0\le h\le d$ and satisfy $\sum_{h=0}^d w_d(h)=1$. Let the increment law be
$p_d(y)=w_d(|y|)/\binom{d}{|y|}$. Both walks start at the origin. CT uses
$\exp(-it(I-P_d))$ with the corresponding convolution matrix $P_d$.
DT starts in coin state $s_y=\sqrt{p_d(y)}$ and applies the coin
reflection $2ss^*-I$ followed by the shift $(y,x)\mapsto(y,x\oplus y)$.
Take position Cesàro limits at each fixed dimension first and push forward
by $|x|/d$ to obtain laws $\nu_{C,d}$ and $\nu_{D,d}$ on $[0,1]$.
The source starts at $d\ge3$. Any admissible extension to lower dimensions
leaves the weak limits along the full dimension sequence unchanged.
[Source models, pp. 2–7](https://arxiv.org/pdf/2611.31635v1#page=2)

For every probability measure $\pi$ on $[0,1]$, if either
$\nu_{C,d}$ or $\nu_{D,d}$ converges weakly to $\pi$, both converge
weakly to $\pi$ if and only if $\Delta_{d,k}\to0$ for every fixed positive
integer $k$. The scalar $\Delta_{d,k}$ is the binomial sum below.
[Issue #34418](https://github.com/the-omega-institute/trureturing/issues/34418)

## Motivation

The examples in §5 show that a spectral gap is neither necessary nor
sufficient for coincidence. The preregistered criterion compares fixed-weight
character expectations of the actual time-averaged position laws and applies
to arbitrary shell eigenvalue coincidences.
[Source discussion](https://arxiv.org/pdf/2611.31635v1#page=14)

## Gap

The issue records a scoped identifier, author and forward-citation search.
It found no answer for the full symmetric kernel family. Griffiths–Mano
supplies related finite coin block formulas, and the earlier path result
concerns a different walk.
[Preregistration search](https://github.com/the-omega-institute/trureturing/issues/34418) · [Griffiths–Mano](https://doi.org/10.3842/SIGMA.2026.063) · [Path result](https://arxiv.org/abs/2301.00283v1)

## Route

Write $\rho_{d,j}$ for the eigenvalue of $P_d$ on characters of weight
$j$, computed from $w_d$ by the normalized Krawtchouk transform. At
$0\le k\le d$, let $u=i+j$, $v=i+k-j$ and
$a_{d,k}(i,j)=2^{-d}\binom{d-k}{i}\binom{k}{j}$, with
$0\le i\le d-k$ and $0\le j\le k$.

$$
\begin{aligned}
\Delta_{d,k}&=\sum_{i,j}a_{d,k}(i,j)\,g_{d,k}(u,v),\\
B_{d,k}&=\sum_{i,j}a_{d,k}(i,j)\,\mathbf{1}_{\{\rho_{d,u}=\rho_{d,v}\}},\\
g_{d,k}(u,v)&=
\begin{cases}
\dfrac{1-\rho_{d,k}}{2(1-\rho_{d,u}^{2})},&
   \rho_{d,u}=\rho_{d,v},\quad |\rho_{d,u}|<1,\\
0,&\text{otherwise}.
\end{cases}
\end{aligned}
$$

In order zero, $B_{d,0}=1$ and $\Delta_{d,0}=0$.
The Walsh pair averages give $B_{d,k}$ for CT and
$B_{d,k}-\Delta_{d,k}$ for DT. The two equal endpoint cases contribute one
in both laws. Unequal numerical eigenvalues contribute zero in both.
Coordinate exchangeability and the sampling comparison bound each Walsh
coefficient's error against the shifted radial moment by $k(k-1)/d$.
The shifted moments characterize weak convergence on the compact unit
interval.

A common weak probability limit exists if and only if, for every fixed
$k\ge1$, $\Delta_{d,k}\to0$ and $B_{d,k}$ has a real limit.
If CT converges weakly to $\pi$, then
$B_{d,k}\to\int_{[0,1]}(1-2x)^k\,d\pi(x)$ for every natural $k$.
Those moments determine the common measure uniquely. The collision
condition supplies existence when a weak limit is unavailable.

## Falsifier

A symmetric family with an existing weak limit and vanishing fixed-weight
gaps but without coincidence, or a common weak limit with a nonvanishing
fixed-weight gap, would falsify the preregistered equivalence. The finite
formula would already fail if its Walsh expectation differed from the
actual position-law average for any admissible kernel and character.

For the scope of the existence criterion, use zero increments in even
dimensions and deterministic all-ones increments in odd dimensions. The
two time-averaged radial laws agree at every dimension. They alternate
between $\delta_0$ and $(\delta_0+\delta_1)/2$. Every gap vanishes, while
$B_{d,1}$ alternates between one and zero. This elementary example
separates the collision condition from the vanishing gaps.

## Evidence

The typed resolution host is
`HypercubeWalsh.common_shell_weakLimit_iff_gap` in `Criterion.lean`.
`HypercubeWalsh.exists_common_shell_weakLimit_iff` proves the stronger
existence-inclusive theorem.
`HypercubeWalsh.shell_continuous_tests_gap_iff` equates vanishing gaps with
asymptotic agreement on every continuous test.
`HypercubeWalsh.tendsto_shell_collisions_to_shiftedMoment` identifies the
collision limits. `HypercubeWalsh.tendsto_finite_shell_gap` and
`HypercubeWalsh.tendsto_finite_shell_collisions` identify the limits of the
actual time-averaged observables. The owner replay uses the ordinary
Mathlib backend and the public axiom closure is `Classical.choice`,
`Quot.sound` and `propext`.

## Triage

The theorem addresses the published coincidence question in the full
preregistered family. The joint-existence criterion additionally decides
when the coincidence has a weak limit to refer to. The §3.9 information
audit remains incomplete and is tracked through the linked issue.
[Issue #34418](https://github.com/the-omega-institute/trureturing/issues/34418)

## ASSUMED-UNVERIFIED

The literature evidence is limited to the preregistered scope. The
alternating-family illustration is an elementary consequence of the
model and is presented here as prose. Canonical repository admission and
resolution projection require native deposit and the current compiler report.
