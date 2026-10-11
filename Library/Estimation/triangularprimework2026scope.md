---
bibkey: triangularprimework2026scope
authors: trureturing research synthesis
year: 2026
title: A conditional all-center obstruction for the actual shrinking triangular prime work
doi: null
url: https://doi.org/10.2298/PIM0476081K
claim: A paper application of the classical explicit formula and positive Gaussian testing, conditional on RH, rules out an eventual finite lower bound for the actual triangular work normalized by h squared over square root A at all real centers; it does not decide the selected-source lower estimate.
strata_touched: []
license: citation-only
triage: anchor
---

# Conditional scope of a uniform triangular-work lower estimate

The actual forward consumer in the
[Nicolas note](../ArithSums/nicolas2025comparison.md#the-exact-forward-successor-on-the-same-original-integer)
uses

$$
w(t)=\frac{1+\log t}{t^2\log^2t},\qquad
T_\psi(A,h)=\int_0^h
[\psi(A+u)-\psi(A)-u]\frac{w(A+u)}{w(A)}\,du.
$$

$\psi$ is the actual Chebyshev prime-power sum, with every
$\Lambda(n)$ weight retained. A lower reference atom at $A$ is
excluded; an upper atom at $A+h$ has zero integrated weight.
The existing sufficient condition asks for a favorable lower estimate
on particular original maximizing sources beyond every required
common finite start. It does not ask for that lower estimate at all
real centers.

The following is a conditional paper argument, with no Lean
verification or general literature-novelty claim. It reuses the
classical RH estimate $\psi(x)-x=O(\sqrt x\log^2x)$, the
distributional explicit formula, the Riemann–von Mangoldt zero count,
and simultaneous recurrence of finitely many real frequencies.
The Gaussian explicit-formula supplier is already recorded in the
[Nicolas note's real-parameter Gaussian interface](../ArithSums/nicolas2025comparison.md#scope-of-the-gaussian-single-zero-sum-formula):
Kamiya–Suzuki, *An asymptotic formula for a sum involving zeros of
the Riemann zeta-function*, Lemma 2.1,
[DOI 10.2298/PIM0476081K](https://doi.org/10.2298/PIM0476081K).
That formula itself is unconditional. RH is an explicit additional
premise throughout the application below, not a derived conclusion.

## Actual shrinking-window normalization

Fix $0<\alpha<1$ and set $h=A^\alpha$. The paper claim is

$$
\boxed{\text{assuming RH},\qquad
\liminf_{A\to\infty}
\frac{\sqrt A}{A^{2\alpha}}T_\psi(A,A^\alpha)=-\infty.}
\tag{TW1}
$$

Thus, even under RH, no finite constant $K$ can give
$T_\psi(A,A^\alpha)\ge-K A^{2\alpha-1/2}$ at every sufficiently
large real $A$. At $\alpha=4/5$, the scale is exactly $A^{11/10}$,
the scale in the selected-source consumer. This compares quantifiers;
it does not refute that consumer's existence statement on its actual
source family.

## A positive Gaussian sees the density derivative

Write $y=\log A$ and

$$
E(y)=e^{-y/2}[\psi(e^y)-e^y],\qquad
S=E'+\tfrac12E,
$$

where the derivative is distributional. Under RH, $E(y)$ has at
most quadratic growth as $y\to+\infty$, and $E(y)=-e^{y/2}$
for $y<\log2$. Hence $S$ is a tempered distribution. Its actual
arithmetic form is

$$
S(y)=\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}\,
\delta_{\log n}(y)-e^{y/2}.
\tag{TW2}
$$

Let $G_\sigma(v)=(\sqrt{2\pi}\sigma)^{-1}
e^{-v^2/(2\sigma^2)}$, with fixed $\sigma>0$. The classical
distributional explicit formula, tested with this Gaussian, gives

$$
\langle S,G_\sigma(\,\cdot-t)\rangle
=-\sum_\rho e^{i\gamma_\rho t}
e^{-\sigma^2\gamma_\rho^2/2}+o(1),\qquad t\to\infty,
\tag{TW3}
$$

under RH. Every actual zero occurs with its multiplicity and both
conjugate signs. The derivative $E'+E/2$ cancels the $1/\rho$
coefficient of the usual $\psi$ explicit formula. The constant
$-\log(2\pi)$ has derivative zero; the trivial-zero derivative
decays on every fixed positive half-line. A smooth cutoff below
a fixed positive $y$ contributes $o(1)$ against the translated
Gaussian. Riemann–von Mangoldt makes the displayed zero sum
absolutely convergent at each fixed $\sigma$.

This is an application of the existing explicit formula, not a new
trace formula. In the Kamiya–Suzuki notation
$H(u,v)=\sum_\rho e^{u\rho^2-v\rho}$, the real-parameter
correspondence is $u=\sigma^2/2$, $v=u-t$:

$$
e^{-t/2+u/4}H(u,u-t)
=\sum_\rho e^{-u\gamma_\rho^2}e^{i\gamma_\rho t}
\qquad\text{under RH}.
$$

The Gaussian width is fixed while $t$ tends to infinity. No
uniform small-width asymptotic from the external paper is assumed.

## Transport the complete triangular work before taking a limit

For large $y$ put

$$
F_\alpha(y)=e^{(1/2-2\alpha)y}
T_\psi(e^y,e^{\alpha y}),\qquad
\epsilon_y=e^{-(1-\alpha)y}.
$$

Multiply by a fixed smooth cutoff equal to one for $y\ge2$ and
zero for $y\le1$, and extend by zero to the left. This changes
no eventual lower-bound statement. Finite interval integration
followed by the change $s=e^y+e^{\alpha y}r$, $0\le r\le1$,
gives the exact distributional representation, before this cutoff,

$$
F_\alpha(y)=\int_0^1 a_y(r)
S\bigl(y+\log(1+\epsilon_y r)\bigr)\,dr,
\tag{TW4}
$$

$$
a_y(r)=(1+\epsilon_y r)^{-1/2}
\int_r^1\frac{w(e^y(1+\epsilon_y s))}{w(e^y)}\,ds.
$$

The equality means pullback and averaging of the distribution in
(TW2); the resulting locally integrable function agrees with the
original work except at irrelevant endpoint values. It retains
all prime-power atoms. To verify the factor, first swap the finite
triangular integral with $d[\psi(s)-s]$ on $(A,A+h]$. Its inner
weight is $h\int_r^1 w(A+hv)/w(A)\,dv$, and
$d[\psi(e^z)-e^z]=e^{z/2}S(z)\,dz$. The factors
$\sqrt A/h^2$, $h$, $\sqrt A\sqrt{1+\epsilon r}$ and
$\epsilon/(1+\epsilon r)$ combine to $(1+\epsilon r)^{-1/2}$.

For each $r$, the map $g_r(y)=y+\log(1+r\epsilon_y)$ is
strictly increasing, since

$$
g_r'(y)=\frac{1+\alpha r\epsilon_y}{1+r\epsilon_y}>0.
$$

For $y\ge2$, uniformly in $0\le r\le1$, the coefficient
$a_y(r)$ and its first two $y$ derivatives differ from
$1-r$, $0$, $0$ by $O_\alpha(\epsilon_y)$.
The shift $g_r(y)-y$ and its first two derivatives are also
$O_\alpha(\epsilon_y)$, and $g_r'(y)$ is bounded below by
$\alpha$. These bounds follow from the displayed formulas; their
constants are independent of the large translation $t$.

Changing variables separately in every pullback gives an adjoint
Gaussian test $H_t$ for (TW4). The preceding bounds give

$$
\int_{\mathbb R}(1+|z|)^2
\left(|H_t(z)-\tfrac12G_\sigma(z-t)|+
|H_t'(z)-\tfrac12G_\sigma'(z-t)|\right)dz=o(1).
\tag{TW5}
$$

Indeed the part with $z\ge2$ is bounded by a constant times
$(1+t)^2e^{-(1-\alpha)t}$ after integrating the fixed-width
Gaussian and its derivatives; the cutoff part has a polynomial
times Gaussian decay in $t$. The factor $1/2$ is exactly
$\int_0^1(1-r)dr$, not an imposed normalization of the atoms.
Since $S=E'+E/2$ and $|E(z)|\ll(1+|z|)^2$, (TW5) proves

$$
\int_{\mathbb R}G_\sigma(v)F_\alpha(t+v)dv
=\tfrac12\langle S,G_\sigma(\,\cdot-t)\rangle+o(1).
\tag{TW6}
$$

Only a weak, Gaussian-tested limit is used. There is no claim
that the sharply sampled density distribution has a pointwise
function limit, or that $S$ itself is bounded.

## Simultaneous recurrence forces arbitrarily negative averages

Combine (TW3) and (TW6), pairing conjugate ordinates:

$$
\int_{\mathbb R}G_\sigma(v)F_\alpha(t+v)dv
=-\sum_{\gamma>0}m_\gamma
e^{-\sigma^2\gamma^2/2}\cos(\gamma t)+o(1).
\tag{TW7}
$$

The coefficients are positive and absolutely summable. Simultaneous
recurrence of every finite list of ordinates, followed by its
absolutely bounded tail, gives

$$
\liminf_{t\to\infty}
\int_{\mathbb R}G_\sigma(v)F_\alpha(t+v)dv
=-\sum_{\gamma>0}m_\gamma e^{-\sigma^2\gamma^2/2}.
\tag{TW8}
$$

No linear-independence hypothesis is needed: simultaneous recurrence
approximates phase zero, and makes no prescription of independent
nonzero phases. The sum on the right tends to infinity as
$\sigma\downarrow0$, because there are infinitely many actual
positive zero ordinates, with multiplicities retained.

If $F_\alpha(y)\ge-K$ eventually for a finite $K$, positivity
and unit mass of every fixed $G_\sigma$ would make the left
liminf at least $-K$. The bounded initial interval contributes
$o(1)$ to the translated average. Choose a fixed sufficiently
small $\sigma$ with the positive sum in (TW8) greater than $K$.
This contradiction proves the conditional paper claim (TW1).
The two limits are taken in this order: fix $\sigma$, then let
$t\to\infty$, and only then choose a smaller fixed width.

## What this excludes and what it leaves open

For $\alpha=4/5$, an all-center replacement of the actual
$-\kappa A^{11/10}$ lower estimate is excluded by this argument
even under RH. A Gaussian or other positive average cannot be
used to infer that all individual centers have the requested sign.
This does not exclude a favorable cofinal subset, and provides
no information about whether the required original maximizing
sources meet that subset.

The original joint selected-source/prime-error relation remains
unproved. The argument certifies no all-integer Robin range,
no unconditional counterexample to Robin, no RH proof and no
Lean-verified mathematical result. It supplies a concrete
conditional benchmark for the strength of a proposed auxiliary,
using the actual triangular kernel rather than a virtual sign model.
