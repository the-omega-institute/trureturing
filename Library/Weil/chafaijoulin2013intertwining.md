---
bibkey: chafaijoulin2013intertwining
authors: Djalil Chafaï and Aldéric Joulin
year: 2013
title: Intertwining and commutation relations for birth–death processes
doi: 10.3150/12-BEJ433
url: https://arxiv.org/abs/1011.2331v4
claim: Positive weighted-gradient intertwining supplies monotonicity and spectral-gap estimates for birth–death processes. An actual reflected prime-two edge prevents radial monotonicity of the original even theta semigroup, so this scalar positive radial derivative interface cannot be transported directly.
strata_touched: []
license: bibliographic-reference-only
triage: anchor
---

# Positive derivative transport and the reflected theta prime edge

## Reuse the published theorem with its actual hypotheses

The journal reference is *Bernoulli* 19(5A) (2013), 1855–1879.
The inspected [arXiv electronic reprint](https://arxiv.org/pdf/1011.2331v4) has
SHA-256 `38a233ff5a9c4aa95876288b268c8f3919671a5373c14c7b3612c24d195cc990`.
Only bibliographic metadata and the model application are retained;
no PDF, implementation or source text is copied into the project.
The reprint explicitly has different pagination from the journal article;
all theorem page locators below refer to that inspected reprint.

Section2, Theorem2.1, reprint p.4, concerns an irreducible,
nonexplosive birth–death process on $\mathbb N$. For a positive weight
$u$, its discrete derivative is $\partial_u f(x)=(f(x+1)-f(x))/u_x$.
The modified process has birth rate
$\lambda_x^u=(u_{x+1}/u_x)\lambda_{x+1}$ and death rate
$\nu_x^u=(u_{x-1}/u_x)\nu_x$, with the usual zero boundary death rate.
The potential is $V_u(x)=\nu_{x+1}-\nu_x^u+\lambda_x-\lambda_x^u$.
Under the section's transition-rate and potential integrability
assumptions, a lower bound on $V_u$ and bounded $\partial_u f$, it gives

$$
\partial_u P_t f=Q_t\partial_u f,
\qquad
Q_t g(x)=\mathbb E_x\!\left[
 g(X_{u,t})\exp\!\left(-\int_0^tV_u(X_{u,s})ds\right)\right]. \tag{R1}
$$

The Feynman–Kac weight is positive even if the lower-bounded potential
has some negative values. Remark2.4, reprint p.6, obtains propagation
of monotonicity from this identity. Corollary3.3, reprint p.11, gives a
Poincare lower bound from a positive weighted Wasserstein curvature,
using the same birth–death framework and its preceding assumptions.
Those source results are reused, not reproved here. The original theta
process has continuous states and nonlocal Gamma and prime-power jumps;
it is not assigned the birth–death hypotheses.

The relevant proposed interface is weaker than total positivity:
does the original even semigroup preserve functions nondecreasing in
$r=|x|$? The [existing ordered determinant test](karlinmcgregor1959coincidence.md)
only excludes all-times order-two positivity. Its failure alone does
not answer this weaker question. The test below uses a different actual
edge and two ordered averaging probes.

## Keep the original form, domain and all prime powers

Use the [minimal mixed theta form](fukushima2011dirichlet.md), with
$\rho(x)=2\Phi(x)\cosh(x/2)$, $d\nu=\rho\,dx$,
$w_n=\Lambda(n)/\sqrt n$, and the symmetric conductance
$J=J_\Gamma+J_p$ defined there. Let $A\ge0$ be its energy operator on
$\mathcal F_{\min,\mathrm{even}}$ and $P_t=e^{-tA}$.
Write $\psi_\Gamma(t)=e^{-t/2}/(1-e^{-2t})$ to distinguish the Gamma
kernel from the golden conjugate coordinate. The real polarized form is

$$
D(f,g)=\tfrac12\iint(f(y)-f(x))(g(y)-g(x))J(dx,dy).
$$

Set

$$
r_0=\tfrac18,\qquad z_0=\log2-r_0,\qquad 0<\delta<\tfrac1{32}.
$$

Choose a smooth nondecreasing function $H:\mathbb R\to[0,1]$,
zero on $(-\infty,-1/2]$ and one on $[1/2,\infty)$, and put

$$
h_\delta(x)=H((|x|-z_0)/\delta).
$$

It is smooth and even, is nondecreasing in $|x|$, and equals one
outside a compact set. Since $1\in\mathcal F_{\min}$ and
$1-h_\delta\in C_c^\infty$, it belongs to the actual minimal even form
domain. No increasing nonzero compactly supported input is requested.

Choose nonnegative even compact smooth $u_{L,\delta},u_{R,\delta}$,
normalized by $\int u_{L,\delta}d\nu=\int u_{R,\delta}d\nu=1$.
Their positive radial supports lie in the intervals of radius
$\delta/4$ centered at $r_0-\delta$ and $r_0+\delta$, respectively.
These intervals are strictly ordered, and $h_\delta=0$ on both probes.
Write $v_\delta=u_{L,\delta}-u_{R,\delta}$; then
$\langle v_\delta,h_\delta\rangle_\nu=0$.

Where the probes are supported, symmetry of $J$ and $h_\delta=0$ give

$$
-D(u,h_\delta)=\int u(x)b_\delta(x)d\nu(x),
$$

with the following even row function:

$$
\begin{aligned}
b_\delta(r)=\frac1{2\cosh(r/2)}\biggl[&
 \int_{\mathbb R}\Phi(y)\psi_\Gamma(|r-y|)h_\delta(y)dy\\
 &+\sum_{n\ge2}w_n\bigl(
 \Phi(r+\log n)h_\delta(r+\log n)
 +\Phi(r-\log n)h_\delta(r-\log n)\bigr)\biggr]. \tag{R2}
\end{aligned}
$$

This is the row normalization $J/\nu$ for the Markov generator $-A$.
It is twice the FOT kernel normalization $J/(2\nu)$; the one-half in
$D$ is removed by the two symmetric cross terms. Formula(R2) is only
used away from the diagonal where the input vanishes, and does not
assert operator-domain membership for $h_\delta$.

## The reflected prime-two atom switches while the background agrees

For every $r$ in either probe interval,
$h_\delta(r+\log n)=1$ for all $n\ge2$ and
$h_\delta(r-\log n)=1$ for all $n\ge3$.
The sole switched destination is $r-\log2$:

$$
\begin{cases}
h_\delta(r-\log2)=1,&r\in\operatorname{supp}_{\rm rad}u_{L,\delta},\\
h_\delta(r-\log2)=0,&r\in\operatorname{supp}_{\rm rad}u_{R,\delta}.
\end{cases} \tag{R3}
$$

Indeed, its radius $\log2-r$ is at least $z_0+3\delta/4$ on
the left and at most $z_0-3\delta/4$ on the right. The source intervals
are below the transition; the plus destinations and the reflected
$n\ge3$ destinations are above it, with a fixed positive margin.
The coefficient of the switched atom is

$$
a_2(r)=\frac{\log2}{2\sqrt2\cosh(r/2)}\Phi(\log2-r)>0. \tag{R4}
$$

All other prime-power row terms form the same continuous background
on both probes. The original local tail bound
$\Phi(r\pm\log n)\le C_Kn^{-2}$ on a fixed compact $K$ bounds their
series by $C_K\sum_{n\ge2}(\log n)n^{-5/2}<\infty$.
Uniform convergence therefore proves continuity, retaining every prime
power and requiring neither a cutoff nor PNT.

For the Gamma background, restrict the sources to
$|r-r_0|<1/16$. The support where $h_\delta$ is nonzero is separated
from these sources by a fixed positive distance. Thus
$\psi_\Gamma(|r-y|)$ is uniformly bounded there, and $C\Phi(y)$ is an
integrable majorant. As $\delta\downarrow0$ and $r\to r_0$,
$h_\delta(y)\to\mathbf1_{\{|y|>z_0\}}$ except at two Lebesgue-null
endpoints. Dominated convergence gives the same Gamma row limit for
both concentrating probes. It also gives uniform convergence on their
shrinking supports; otherwise a sequence of points in those supports
would contradict the same joint limit. The Gamma diagonal singularity
never enters this computation.

Subtracting the two normalized probe averages in(R2) now yields

$$
I_\delta:=-D(v_\delta,h_\delta)
\longrightarrow a_2(r_0)>0\qquad(\delta\downarrow0). \tag{R5}
$$

The coefficient uses both reflected source halves through normalization
against the even probability measure; no additional factor two is added.

## Short time reverses the ordered averages

Reuse [the form-semigroup derivative (O2)](karlinmcgregor1959coincidence.md#test-the-unchanged-even-form-before-borrowing-oscillation-theory).
For a fixed sufficiently small $\delta$ with $I_\delta>0$, it gives

$$
\langle v_\delta,P_t h_\delta\rangle_\nu
=tI_\delta+o(t)>0
\quad\text{for all sufficiently small }t>0. \tag{R6}
$$

The order of limits matters: first choose $\delta$, then let $t$ tend
to zero. There is no uniform short-time remainder claim as the probes
concentrate. All inputs are in the form domain, as required by(O2).

If $P_t h_\delta$ had a representative nondecreasing in $|x|$, its
average against the normalized left probe could not exceed its average
against the normalized right probe. Equation(R6) reverses that inequality.
Under the inherited original-form and semigroup premises, the argument
therefore excludes all-times radial monotonicity of the original even
semigroup.

In particular, a scalar positive weighted radial first-derivative
intertwiner, valid on these plateau tests and implying preservation of
this monotonicity cone, cannot realize(R1) for this model. That implication
is essential to the exclusion: no claim is made about arbitrary positive
intertwiners, other partial orders, signed or vector transports, or
fixed-time comparisons. Ordinary Markov positivity is unaffected.

## The remaining all-input estimate is unchanged

The application isolates a specific failure of the published method's
proposed radial transport, with all original long edges present. It does
not produce a subthreshold eigenvector or decide the sign of the
[critical remainder](lagarias2004li.md#the-full-derivative-family-and-the-remaining-estimate).
The still-needed estimate is $D(r)\ge\|r\|_\nu^2/2$ on that remainder,
or actual cofinal low-center signs sufficient for the same original
half-bound. A five-mode FIB tiling may label the sources and destinations,
but those labels do not remove the reflected map $r\mapsto|\log2-r|$.

The source mapping and equations(R2)–(R6) are conditional paper
mathematics, not Lean certification, a new general method or a priority
claim. No fixed-target action, moment, Gram or numerical producer is
replayed. Cofinal positivity, the half-bound, full Robin and RH remain
unresolved.
