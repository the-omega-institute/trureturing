---
bibkey: jarohsweth2020local
authors: Sven Jarohs and Tobias Weth
year: 2020
title: Local compactness and nonvanishing for weakly singular nonlocal quadratic forms
doi: 10.1016/j.na.2019.01.021
url: https://arxiv.org/abs/1811.12850v1
claim: The source supplies local compactness and a quantitative averaging estimate for a weakly singular comparison kernel. Original-model cutoff and graph estimates transport them to uniform finite-rank approximation in the mixed minimal form norm, with explicit analytic bounds but no computed lower spectral certificate.
strata_touched: []
license: bibliographic-reference-only
triage: anchor
---

# Local compactness in the actual theta measure

## Inspected source and comparison space

The journal record is *Nonlinear Analysis* 193 (2020), article 111431.
The inspected primary text is [arXiv:1811.12850v1](https://arxiv.org/pdf/1811.12850v1),
with SHA-256
`70b2bff55e07835ed9d94c6852e9e2e81b1c14f4b4e6c4e5ec637c07f18648dc`.
The publisher full text was not retrieved; equality with that edition is
not asserted. Theorem 1.1, printed p.3, assumes the even measurable kernel
$j\ge0$ satisfies (A1), printed p.2, and (A2), printed p.3:

$$
0<\int(1\wedge |z|^2)j(z)\,dz<\infty,
\qquad \int j(z)\,dz=\infty.
$$

For
$\mathcal E_j(g)=\frac12\iint |g(y)-g(x)|^2j(y-x)\,dx\,dy$,
the theorem makes the finite-energy-domain inclusion into $L^2(dx)$
compact after restriction to every compact set. No strictly positive
fractional order is required. We reuse this theorem rather than prove a
new logarithmic-frequency compactness theorem. Complexification preserves
the compactness conclusion.

In one dimension take

$$
j_0(z)=\frac{\mathbf1_{\{0<|z|<1\}}}{|z|}.
$$

Its second-moment integral is $1$ and its total integral is infinite,
so both source hypotheses hold.

## The cutoff map from the theta minimal domain

Use the measure and Gamma energy of the
[actual minimal mixed realization](fukushima2011dirichlet.md):
$\rho=2\Phi\cosh(x/2)$, $d\nu=\rho\,dx$ and
$\psi(t)=e^{-t/2}/(1-e^{-2t})$. Let $\mathcal F_\Gamma$ be the minimal
closure of the full compact smooth core for $D_\Gamma=E_\Gamma$.
The same source construction applies with the prime measure omitted;
this defines the Gamma operator, not a replacement for the full energy.

For compact $K$, choose a real $\chi\in C_c^\infty$, equal to one near
$K$, and let the compact interval $I$ contain
$\operatorname{supp}\chi+[-1,1]$. Put

$$
m_\Phi=\min_I\Phi>0,\qquad m_\rho=\min_I\rho>0,
\qquad c_\psi=\inf_{0<t<1}t\psi(t)>0.
$$

For a core function $h$, use

$$
|\chi(y)h(y)-\chi(x)h(x)|^2
\le2|\chi(y)|^2|h(y)-h(x)|^2
+2|\chi(y)-\chi(x)|^2|h(x)|^2.
$$

For $|x-y|<1$, every nonzero cutoff term has both endpoints in $I$.
On these pairs the Gamma conductance is at least
$m_\Phi^2c_\psi/|x-y|$. Also
$|\chi(y)-\chi(x)|\le\|\chi'\|_\infty|x-y|$ and
$\int_{|t|<1}|t|\,dt=1$. The exact one-half energy convention therefore gives

$$
\begin{aligned}
\mathcal E_{j_0}(\chi h)
&\le\frac{2\|\chi\|_\infty^2}{m_\Phi^2c_\psi}D_\Gamma(h)
+\frac{\|\chi'\|_\infty^2}{m_\rho}\|h\|_\nu^2,\\
\|\chi h\|_{L^2(dx)}^2
&\le\frac{\|\chi\|_\infty^2}{m_\rho}\|h\|_\nu^2.
\end{aligned} \tag{LC}
$$

The comparison domain is closed. Applying (LC) to differences of core
approximants extends this bounded cutoff map to $\mathcal F_\Gamma$;
its $L^2(dx)$ limit is $\chi h$ by local equivalence of the two measures.
The source theorem then gives compact restriction to $K$, and boundedness
of $\rho$ there converts the convergence to $L^2(\nu)$. Thus
$\mathbf1_K:\mathcal F_\Gamma\to L^2(\nu)$ is compact.

This does not identify the theta minimal domain with the comparison
kernel's maximal finite-energy space. It does not apply a density-kernel
theorem directly to prime atoms or infer global compactness from
$\nu(\mathbb R)=1$. The bounded prime energy in the
[mixed spectral application](lenz2010compactness.md) transports this local
compactness to the original mixed minimal domain.

The cutoff estimate and source application are paper-level model checks,
without new Lean certification or an originality claim. They supply no
one-half global Poincare constant.

## Quantitative finite-rank approximation in the original form norm

This section transports an existing weak-singularity averaging estimate
into the original mixed minimal form space. It gives a finite-rank
existence construction with an explicit error and rank bound. It does not
supply computed singular functions or a lower spectral matrix.

### Reuse the source averaging estimate

Jarohs–Weth, Lemma 2.2, printed pp.7–8 of the inspected v1, states

$$
\|u-w_\delta*u\|_2^2
\le\frac{2}{\|j_\delta\|_1}
          (\|u\|_2^2+\mathcal E_j(u)),
\qquad w_\delta=j_\delta/\|j_\delta\|_1.
$$

The source norm includes the $L^2$ term. Reuse this lemma, with
$j=j_0=\mathbf1_{\{0<|t|<1\}}/|t|$, rather than reprove its Jensen or
compactness argument. For $\ell>0$, $\delta=e^{-\ell}$,

$$
w_\delta(t)=\frac{\mathbf1_{\{\delta<|t|<1\}}}{2\ell|t|},
\qquad \|j_\delta\|_1=2\ell.
$$

Write $L_0$ for the whole-line self-adjoint operator of
$\mathcal E_{j_0}$ in $L^2(dx)$, and
$\|u\|_{\mathcal F}^2=\|u\|_\nu^2+D(u)$ for the original mixed minimal
form norm. The comparison operator is used only for estimates; the
arithmetic energy and original measure are retained.

### An operator comparison for compact low-space cuts

Fix $0<\varepsilon\le1/2$, $R\ge R_{\rm PNT}(\varepsilon)$ and a unit
vector in the actual even low subspace
$h\in\operatorname{ran}\mathbf1_{[0,1/2-\varepsilon]}(A_{\rm even})$.
Let $\chi_R=1-\eta_R$, $g=\chi_Rh$, and put

$$
L=R+2,\quad I=[-L,L],\quad J=[-R-4,R+4],\quad z=R+4,
$$

$$
m=18e^{-4e^{2z}},\quad W=\frac{36}{5}\cosh(z/2),
\quad a_*=\frac{m}{2\cosh(z/2)},
\quad B=\frac4{m^2}+\frac1m.
$$

The [original theta constants](../Analytic/romik2021orthogonal.md) give
$\rho\le W$ on $J$. The first positive theta summand, used only for a
lower estimate, gives for $|x|\le z$

$$
\Phi(x)\ge2\pi(2\pi-3)e^{-\pi e^{2z}}
\ge18e^{-4e^{2z}}=m,
\qquad \rho(x)\ge2m.
$$

Here evenness, $3<\pi<4$ and $e^{|x|/2}\ge1$ are used; the remaining
positive summands remain in the original operator. Also
$t\psi(t)\ge1/4$ on $0<t<1$. Thus (LC), with
$\|\chi_R\|_\infty,\|\chi_R'\|_\infty\le1$ and
$D_\Gamma(h)\le D(h)\le1/2$, yields

$$
\|g\|_2^2\le\frac1{2m},\qquad
\|g\|_2^2+\mathcal E_{j_0}(g)\le B. \tag{IB}
$$

The full low-subspace commutator estimate in the
[mixed spectral note](lenz2010compactness.md) gives $g\in D(A_\Gamma)$.
With $M=\|a_p\|_\infty<432$, (BD) implies
$-2M\le B_p\le M$ in operator order, so $\|B_p\|\le2M$.
Since $A_\Gamma h=Ah-M_{a_p}h+B_ph$ and
$\|[A_\Gamma,\eta_R]\|\le4e^{-R}\le4$,

$$
\|A_\Gamma g\|_\nu\le1301. \tag{IG}
$$

To compare operator domains, decompose

$$
\psi(|t|)=\tfrac12j_0(t)+k(t),\qquad \|k\|_1<7.
$$

For $0<t<1$, the inequalities
$1/(2t)\le(1-e^{-2t})^{-1}\le1+1/(2t)$ and
$1-e^{-t/2}\le t/2$ give $-1/4\le k(t)\le1$.
For $|t|\ge1$, the previous $d e^{-|t|/2}$ bound gives a two-sided
integral below $14/3$, hence the claimed $L^1$ bound.
Let $L_ku=\int k(t)(u-\tau_tu)\,dt$, so $\|L_k\|\le14$.
For $d(x)=2\cosh(x/2)$ and $a(x)=\Phi(x)/d(x)$ define

$$
\mathsf Ru(x)=\frac1{d(x)}\int
   (\Phi(y)-\Phi(x))\psi(|x-y|)(u(x)-u(y))\,dy.
$$

The source bounds $|\Phi'|\le60$ and $\Phi\le18/5$ give
$|\Phi(y)-\Phi(x)|\psi(|x-y|)\le90$ for $0<|x-y|<1$.
For longer jumps its full row integral is at most
$(36/5)(14/3)=168/5$. Dividing by $d(x)\ge2$ gives both absolute
rows and columns of the off-diagonal kernel at most $534/5$.
Its diagonal has the same bound, so the unweighted Schur estimate gives
$\|\mathsf R\|_{L^2(dx)\to L^2(dx)}\le1068/5<214$.
On the compact smooth core the exact identity is

$$
A_\Gamma u=a(x)(\tfrac12L_0u+L_ku)+\mathsf Ru. \tag{OI}
$$

For the actual $g$, compactly supported form-core approximants converge
in the $j_0$ form norm by (LC). Consequently (OI) passes to distributions;
its Gamma side is interpreted through the original form representation,
not an operator-core assumption. Dividing by the positive smooth $a$ on
$J$ and using $g\in D(A_\Gamma)$ shows that $L_0g$ is locally $L^2$
there. The distribution $L_0g$ is supported in $I+[-1,1]$, strictly inside
$J$. Equivalently, the standard whole-line Fourier realization of $L_0$
puts $g$ in its operator domain. Since $a\ge a_*$ on $J$, (IB), (IG)
and (OI) give the uniform bound

$$
\|L_0g\|_2\le G:=\frac{3030/a_*+28}{\sqrt{2m}}. \tag{LG}
$$

The two units of exterior margin in $J$ keep the support/domain argument
inside the region where the density lower bound is available.

### Transport the averaging error into the mixed form

For $u$ supported in $J$, the original conductance and $\Phi\le18/5$
give, retaining every Gamma jump,

$$
D_\Gamma(u)\le\frac{324}{25}
            (\tfrac12\mathcal E_{j_0}(u)+14\|u\|_2^2).
$$

Together with (BD) and $\rho\le W$ on $J$, this yields

$$
\|u\|_{\mathcal F}^2
\le C_0\|u\|_2^2+7\mathcal E_{j_0}(u),
\qquad C_0=865W+182. \tag{UC}
$$

Let $T_\delta u=w_\delta*u$ and $v=g-T_\delta g$.
Its support lies in $I+[-1,1]\subset J$. The reused source lemma gives
$\|v\|_2^2\le B/\ell$. The whole-line convolution commutes with $L_0$,
while $\|I-T_\delta\|\le2$. Hence

$$
\mathcal E_{j_0}(v)
=\langle L_0v,v\rangle
\le2G\sqrt{B/\ell},
\qquad
\|v\|_{\mathcal F}^2
\le C_0B/\ell+14G\sqrt{B/\ell}. \tag{AF}
$$

This uses commutation with the flat comparison operator, not with the
state-dependent original Gamma operator.

### A finite-rank map into the original minimal form domain

View $K_\delta u=T_\delta u$, for $u\in L^2(I;dx)$ extended by zero,
as a map into $\mathcal F$. For its kernel one has

$$
\|w_\delta\|_2^2=\frac{\delta^{-1}-1}{2\ell^2},\quad
\|w_\delta\|_\infty=\frac1{2\ell\delta},\quad
\operatorname{TV}(w_\delta)=\frac2{\ell\delta}.
$$

The standard BV translation bound gives
$\|\tau_tw_\delta-w_\delta\|_2^2
\le2|t|/(\ell^2\delta^2)$, hence
$\mathcal E_{j_0}(w_\delta)\le2/(\ell^2\delta^2)$.
Each translated kernel is supported inside $I+[-1,1]$. Mollification
converges in $L^2$ and in the $j_0$ form norm: the squared translation
differences are dominated by four times those of the original kernel.
On a fixed slightly larger compact interval (UC) then gives convergence
in the original form norm. Thus these kernels belong to the original
minimal domain, without identifying a maximal domain.

The shifted kernels depend continuously in form norm on their center;
they define a measurable Hilbert-space-valued kernel. Its Hilbert–Schmidt
bound into $\mathcal F$ is therefore

$$
\|K_\delta\|_{\mathrm{HS}(L^2(I),\mathcal F)}^2
\le H:=\frac L{\ell^2}
       \left[C_0(e^\ell-1)+28e^{2\ell}\right]. \tag{HS}
$$

Restrict to the even source and target spaces. Reflection commutes with
convolution and the original form, and restriction only decreases the
Hilbert–Schmidt bound. The standard singular-value truncation supplies a
rank-at-most-$N$ map $K_{\delta,N}:L^2_{\rm even}(I)\to\mathcal F_{\rm even}$
with

$$
\|K_\delta-K_{\delta,N}\|\le\sqrt{H/(N+1)}. \tag{SV}
$$

The singular vectors for nonzero singular values lie in the range of
$K_\delta$, so the finite-rank output is supported in $I+[-1,1]$.
Neither the generic singular-value theorem nor the source averaging
lemma is a new project result.

### Uniform finite-rank form approximation and a rank bound

Fix $0<\tau<1$. In addition to $R\ge R_{\rm PNT}(\varepsilon)$, take

$$
R\ge\log\frac{8640}{\varepsilon\tau},\qquad
\ell\ge\max\left\{1,\frac{18C_0B}{\tau^2},
                         B\left(\frac{252G}{\tau^2}\right)^2\right\},
\qquad N+1\ge\frac{9H}{2m\tau^2}. \tag{FP}
$$

For example the ceiling of the last right-hand side is a permissible
$N$. The original full low-projector form-tail estimate gives
$\|h-g\|_{\mathcal F}\le\sqrt{866}(96/\varepsilon)e^{-R}<\tau/3$.
The two terms in (AF) are each at most $\tau^2/18$.
Finally (IB) and (SV) give
$\|K_\delta g-K_{\delta,N}g\|_{\mathcal F}\le\tau/3$.
For the single finite-rank map $V_N=K_{\delta,N}M_{\chi_R}$, these are
simultaneous estimates on the whole actual low subspace, so

$$
\boxed{
\sup_{\substack{h\in\operatorname{ran}P_\varepsilon\\\|h\|_\nu=1}}
                  \|h-V_Nh\|_{\mathcal F}<\tau,
\qquad \operatorname{rank}P_\varepsilon\le N.
} \tag{FA}
$$

The rank conclusion follows because $\tau<1$ makes $V_N$ injective on
that subspace already in $L^2(\nu)$. It includes the constant eigenspace.
Projection onto $\mathcal R$ contracts this form error for vectors in the
remainder, while generally destroying compact support.

The rank and error formulas are analytic upper bounds. The chosen $m$
uses the minimum density on a growing interval; no computational
feasibility, computed singular basis or lower spectral matrix is
supplied. The passage from $L^2$ to form
estimates uses (LG), (UC), (AF) and the form-valued (HS).
A complete lower spectral certificate and control uniform as
$\varepsilon\downarrow0$ remain missing. These model deductions are
paper-level and have no new Lean certification or originality claim;
RH and full Robin remain unresolved.
