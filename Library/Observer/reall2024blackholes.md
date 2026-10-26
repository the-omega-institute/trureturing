---
bibkey: reall2024blackholes
authors: Harvey S. Reall
year: 2024
title: Black Holes
doi: null
url: https://www.damtp.cam.ac.uk/user/hsr1000/black_holes_lectures_2024.pdf
claim: Static Schwarzschild observers have proper acceleration M divided by r squared times the redshift factor in geometric units; local acceleration diverges at the horizon.
strata_touched: []
license: citation-only
triage: anchor
---

# Static Schwarzschild clocks and numerical resource bounds

## Source and correspondence

Reall, *Black Holes*, §9.2, printed p. 116 (PDF p. 117), equations
(9.8)–(9.12), derives the acceleration of a stationary Killing orbit and
then explicitly specializes its norm to Schwarzschild. The source uses
$G=c=1$. In fixed physical units the exterior lapse and the acceleration
of a test observer held at fixed areal radius $R>2GM/c^2$ are

$$
\alpha=\frac{d\tau}{dt}=\sqrt{1-\frac{2GM}{c^2R}},\qquad
 a=\frac{GM}{R^2\alpha}.
$$

Here $M>0$ is the source mass and $t$ is normalized at infinity. These
are `literature-attested` background formulas. See also Sean M. Carroll,
*Lecture Notes on General Relativity*,
[arXiv:gr-qc/9712019](https://arxiv.org/abs/gr-qc/9712019), §7, for the
Schwarzschild exterior. Setting $dR=d\Omega=0$ in the metric gives the
proper-time formula. Scaling $M$ and $R$ by the same positive factor
preserves $\alpha$; source mass alone does not specify a clock ratio.

## Elementary resource consequence

The following is a `repo-derived` algebraic application of these
classical formulas, rather than a result attributed to the source.
Solving for $R$ and substituting gives

$$
R=\frac{2GM}{c^2(1-\alpha^2)},\qquad
Ma=\frac{c^4}{4G}\frac{(1-\alpha^2)^2}{\alpha}.
$$

When $0<\alpha\le1/2$ this implies

$$
Ma\ge\frac{9c^4}{64G}\alpha^{-1}.
$$

Fix numerical units $M_0,a_0>0$. If a family satisfies
$M(n)\le M_0P(n)$ and $a(n)\le a_0Q(n)$, then the two cases
$\alpha\le1/2$ and $\alpha>1/2$ give

$$
1\le\alpha(n)^{-1}\le
\max\left\{2,\frac{64GM_0a_0}{9c^4}P(n)Q(n)\right\}.
$$

For polynomial $P,Q$, the right side has a polynomial majorant. Bounds
on the bit lengths of $M$ and $a$ do not supply these numerical bounds.
For example, requiring $\alpha=2^{-n}$ for $n\ge1$ instead forces
$Ma\ge9c^4 2^n/(64G)$ in this same model. Constant numerical source mass
can achieve an arbitrarily small positive lapse only with unbounded
suspension acceleration; this is why the two upper bounds are used
together.

At fixed $R$, a remote reference interval $T$ corresponds to local
waiting $\tau=\alpha T$, between $T/q$ and $T$ when $1/\alpha\le q$.
The native protocol application and its charged-operation assumptions
are in [Native capacity, §20](../../docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CAPACITY_COHERENCE_AND_GROWTH.md#20-serial-literal-self-images-under-calibrated-clocks).

## Interpretation limits

These are static test-observer statements in a supplied nonrotating
vacuum exterior. They do not construct the gravitating source or the
suspension, bound total energy expenditure, include backreaction,
kinematic time dilation or free fall, or constrain arbitrary spacetimes.
They do not specify the proper duration of a CPU primitive. An ideal
local CPU and a colocated ideal clock acquire the same gravitational
conversion factor relative to $t$; a separate gate implementation is
needed to determine the CPU's local rate. Receiving an external
computation result additionally requires a communication and readout
protocol.

For a differentiable local Schrödinger evolution, the change of parameter
$d\tau=\alpha(t)dt$ gives

$$
i\hbar\frac{d\psi}{dt}
=\alpha(t)H_{\rm loc}(\tau(t))\psi.
$$

This chain-rule identity compares one specified evolution in two
parameters. It does not derive the lapse from information growth or
identify an algorithmic copying cost with a universal gravitational
redshift.
