---
bibkey: jarohsweth2020local
authors: Sven Jarohs and Tobias Weth
year: 2020
title: Local compactness and nonvanishing for weakly singular nonlocal quadratic forms
doi: 10.1016/j.na.2019.01.021
url: https://arxiv.org/abs/1811.12850v1
claim: The source supplies local compactness and a quantitative averaging estimate for a weakly singular comparison kernel. Original-model cutoff and graph estimates transport them to uniform finite-rank approximation in the mixed minimal form norm, with explicit analytic bounds and a prescribed translated-kernel spanning family, and a directed finite matrix assembly interface, but no computed lower spectral certificate.
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

## Explicit translated kernels and the legal FIB mesh

The original-form graph transfer and (IB), (UC), (AF), (FP) also give a
prescribed finite spanning family, without using unknown singular
functions. Fix $0<\varepsilon\le1/2$ and $0<\tau<1$; retain the preceding
$R,\ell,m,C_0,B,G,L,I,J$, using the radius and averaging choices of (FP)
but replacing its SVD rank choice by the mesh below. For a unit even
$h\in\operatorname{ran}P_\varepsilon$, put $g=\chi_Rh$ and
$w=w_\delta$, $\delta=e^{-\ell}$. Standard BV translation estimates,
Hilbert-space kernel estimates and the existing FIB interval tiling are
reused here. The model interface is their uniform error estimate in the
original mixed minimal form norm.

### Translation modulus in the original form norm

Set $A_\delta=2/(\ell^2\delta^2)$. The reused BV translation inequality
gives $\|\tau_sw-w\|_2^2\le A_\delta|s|$. For $0<s\le1$ and
$v_s=\tau_sw-w$, commuting flat translations and the triangle inequality
give

$$
\|\tau_tv_s-v_s\|_2^2
\le4A_\delta\min(s,t)\qquad(0<t<1).
$$

Using the existing one-half energy convention,

$$
\mathcal E_{j_0}(v_s)
=\int_0^1\|\tau_tv_s-v_s\|_2^2\frac{dt}{t}
\le4A_\delta s(1+\log(1/s)). \tag{TM}
$$

For $y,c\in I$, $|y-c|\le\Delta\le1$, the kernels lie in the previously
proved original minimal domain and are supported in $I+[-1,1]\Subset J$.
Apply (UC) to their difference. The function $s(1+\log(1/s))$ is
nondecreasing on $(0,1]$, hence

$$
\|w(\cdot-y)-w(\cdot-c)\|_{\mathcal F}^2
\le A_\delta\Delta[C_0+28(1+\log(1/\Delta))]. \tag{FM}
$$

At $y=c$ the difference is zero. This bound also supplies continuity and
Bochner measurability of the form-valued kernel. It uses full original
form upper comparison, not a prime truncation or convolution commutation
with $A_\Gamma$.

### A prescribed symmetric mesh map

Partition $I$ into cells $I_j$ of maximal width $\Delta\le1$, using
half-open cells at endpoints of measure zero, and take their midpoints
$c_j$. Define

$$
K^{\rm mesh}u(x)=\sum_j w(x-c_j)\int_{I_j}u(y)\,dy.
$$

The Hilbert-space-valued kernel bound (FM) gives

$$
\|K_\delta-K^{\rm mesh}\|_{\rm HS(L^2(I),\mathcal F)}^2
\le2LA_\delta\Delta[C_0+28(1+\log(1/\Delta))].
$$

For the actual $g$, (IB) states $\|g\|_2^2\le1/(2m)$, so

$$
\|K_\delta g-K^{\rm mesh}g\|_{\mathcal F}^2
\le\frac{LA_\delta}{m}\Delta[C_0+28(1+\log(1/\Delta))]. \tag{ME}
$$

Use $\Delta\le\sqrt\Delta$ and
$\Delta(1+\log(1/\Delta))\le2\sqrt\Delta$ to set

$$
d_*:=\min\left\{1,
\left[\frac{m\tau^2}{9LA_\delta(C_0+56)}\right]^2\right\}. \tag{MS}
$$

Every mesh of maximal width at most $d_*$ makes (ME) at most $\tau^2/9$.
For a symmetric partition with zero inserted, list its positive cells
$I_j^+$ and midpoints $c_j>0$. Define the explicit even real functions

$$
b_j(x)=w(x-c_j)+w(x+c_j),\qquad
Vh=\sum_j b_j(x)\int_{I_j^+}\chi_R(y)h(y)\,dy. \tag{EB}
$$

For even $h$ this equals $K^{\rm mesh}g$. Each $b_j$ belongs to the
original minimal form domain by the already proved kernel membership;
no eigenfunction or singular-vector computation is used. The outer
error is $<\tau/3$ by (FP); the averaging error is $\le\tau/3$ by (AF);
the mesh error is $\le\tau/3$ by (MS). Thus the single prescribed map
satisfies

$$
\sup_{h\in\operatorname{ran}P_\varepsilon,\ \|h\|_\nu=1}
\|h-Vh\|_{\mathcal F}<\tau. \tag{EA}
$$

The real spanning family need not be linearly independent; matrix PSD
on that family is nevertheless equivalent to form nonnegativity on its
span. Its size is a rank upper bound; no computed Gram matrix is given.

### Reuse the existing FIB five-mode interval partition

Use the existing
[FIB interval tiling](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md)
§§150–151 and
[legal address graph](../../docs/develop/theory/FIB_SOURCE_COMPLETION_DYNAMICS.md)
Definition 14.5 and Proposition 14.6.
Their graph is
$0\to0:\mathrm{null},2,3$; $0\to1:25,5$;
$1\to0:\mathrm{null},3$; $1\to1:5$.
Their contraction is $\lambda=-\phi^{-3}$ and state intervals are
$K_0=[-1,\phi]$, $K_1=[-1,\phi^{-1}]$. Legal cylinder intervals tile
with disjoint interiors; shared endpoints have zero length measure.

At depth $n$, the state-zero partition has $p_n=F_{3n+2}$ intervals
(the count of no-adjacent-one bit strings of length $3n$), with maximal
width $\phi^2\phi^{-3n}$, where $F_0=0,F_1=1$. The affine map

$$
y=-L+\frac{2L}{\phi^2}(t+1)
$$

sends it to a partition of $I$ of maximal width $2L\phi^{-3n}$.
Take the common refinement with its reflection and insert zero. There
are at most $2p_n$ cells: the two original endpoint sets share $-L,L$,
and insertion of zero adds at most one endpoint. Symmetry pairs all
positive and negative cells, so (EB) uses at most $p_n$ functions. Take

$$
n\ge\left\lceil\frac{\log(2L/d_*)}{3\log\phi}\right\rceil. \tag{FD}
$$

Then (EA) holds and, because $\tau<1$, $V$ is injective on the low
subspace in $L^2(\nu)$, giving $\operatorname{rank}P_\varepsilon\le p_n$.
FIB labels index this mesh only; they are not prime weights, and no
active golden rotation of the single contracting interval is asserted.
An ordinary sufficiently fine symmetric mesh gives the same guarantee;
the FIB addressing supplies no proved improvement in approximation rate.

### A conditional finite matrix target with completeness paid

For the fixed-gap target, use the explicit approximation above with

$$
a=\tfrac12-\varepsilon,\qquad
c_\varepsilon=\tfrac12-\varepsilon/2,\qquad
\tau=\varepsilon/8.
$$

Let $Y=\operatorname{span}\{b_j\}$ and
$\mathcal W_c(v)=D(v)-c\operatorname{Var}_\nu(v)$, where
$\operatorname{Var}_\nu(v)=\|v-\langle1,v\rangle_\nu1\|_\nu^2$
and $\langle u,v\rangle_\nu=\int\overline u v\,d\nu$.
Because the spanning functions are real and $\nu(\mathbb R)=1$, its
exact Hermitian matrix is

$$
T_{ij}^{(\varepsilon)}=D(b_i,b_j)-c_\varepsilon
\left[\langle b_i,b_j\rangle_\nu-\mu_i\mu_j\right],
\qquad \mu_i=\int b_i\,d\nu. \tag{MT}
$$

Here $D(\cdot,\cdot)$ is the sesquilinear polarization of the complete
prime-plus-Gamma energy, retaining every prime power and crossing edge.
Suppose (MT) is verified positive semidefinite. If a mean-zero unit $h$
were in $\operatorname{ran}P_\varepsilon$, then $D(h)\le a$ and
$\mathcal W_{c_\varepsilon}(h)\le-\varepsilon/2$. For $v=Vh$, (EA),
Cauchy–Schwarz for the energy form and the norm-one projection onto
constants' complement give

$$
|\mathcal W_{c_\varepsilon}(v)-\mathcal W_{c_\varepsilon}(h)|
\le[2\sqrt a+2c_\varepsilon+(1+c_\varepsilon)\tau]\tau
\le3\tau\qquad(\tau\le1/3).
$$

Thus $\mathcal W_{c_\varepsilon}(v)<-\varepsilon/8$, contradicting
PSD on $Y$. The conditional conclusion is

$$
T^{(\varepsilon)}\succeq0
\quad\Longrightarrow\quad
\operatorname{ran}P_\varepsilon\subseteq\mathbb C1. \tag{PC}
$$

This conclusion covers the whole fixed-gap window because (EA) is
uniform on its actual spectral subspace. Generic matrix PSD and form
perturbation are reused, not new spectral theorems. The finite hypothesis
requires the lower level $c_\varepsilon<1/2$: on the same span,
half-threshold PSD implies this condition since
$\mathcal W_{c_\varepsilon}=\mathcal W_{1/2}
+(\varepsilon/2)\operatorname{Var}_\nu$. This implication certifies no
actual matrix sign or strict separation of signs.

The entries and signs in (MT) are uncomputed; (PC) is not an actual
lower spectral certificate. A cofinal sequence
$\varepsilon\downarrow0$, or a separate uniform theorem, is still
needed to exclude every nonconstant spectral value below one-half.
The bounds do not establish computational feasibility. These explicit
model transfers are paper-level, without new Lean certification or an
originality claim; RH and full Robin remain unresolved.

## Directed assembly for the actual mixed theta matrix

Reuse the original-domain even real family $b_1,\ldots,b_q$,
$b_j(x)=w_\delta(x-c_j)+w_\delta(x+c_j)$, $\delta=e^{-\ell}$, and all
previous form/domain estimates. Let $S=L+1$, $K=[-S,S]$ and
$B(x)=(b_1(x),\ldots,b_q(x))^T$, with $B=0$ off $K$.
The exact target is $T_\varepsilon=D-c_\varepsilon(G-\mu\mu^T)$,
$c_\varepsilon=1/2-\varepsilon/2$, $\nu(\mathbb R)=1$.

### Exact same-object matrices

$$
G=\int_K B(x)B(x)^T\rho(x)dx,\quad
\mu=\int_K B(x)\rho(x)dx,\quad \rho=2\Phi\cosh(x/2),
$$

$$
\begin{aligned}
D_\Gamma&=\int_{x<y}\Phi(x)\Phi(y)\psi(y-x)
 [B(y)-B(x)][B(y)-B(x)]^Tdxdy,\\
D_p&=\sum_{n\ge2}w_n\int_{\mathbb R}\Phi(x)\Phi(x+\log n)
 [B(x+\log n)-B(x)][B(x+\log n)-B(x)]^Tdx,
\quad w_n=\Lambda(n)/\sqrt n.
\end{aligned} \tag{DM}
$$

The positive-shift prime integral includes both original shifted graph
terms after change of variables, cancelling the one-half prefactor.
There is no further factor two. These are the original minimal-domain
energies, with every prime power and Gamma crossing.

For $H>S$, $N\ge2$ an integer, retain the Gamma square $[-H,H]^2$ and
the complete prime terms $n\le N$. Call their sum $D_{H,N}$. Before
expanding differences, each omitted region contributes a positive weight
times an outer product, so

$$
D-D_{H,N}=R_\Gamma+R_p\succeq0. \tag{DE}
$$

This is a simultaneous coefficient-vector inequality, not entrywise
positivity of the energy matrices or of their off-diagonal entries.

### Reuse validated analytic quadrature

The [Johansson/FLINT integration supplier](../Analytic/johansson2018ballintegration.md)
provides the existing validated Petras method and the bounded-path,
holomorphic-callback contract. Reuse its documented one-dimensional Gauss
error $M e_n(r)$, where $e_n(r)=64/[15(r-1)r^{2n-1}]$.
Finite endpoints, bounded integrands and inspection of the returned
ball are necessary. The quadrature result and implementation are
existing work; the actual-model integration interface follows below.

### Remove both smooth-diagonal and jump-corner singularities

Partition $[-H,H]$ at all $\pm c_j\pm\delta$, $\pm c_j\pm1$ and its
endpoints. On each open interval $B$ is a fixed rational branch, with
denominators separated from zero on its closure. Use one-sided branches
at endpoints; their point values do not affect either Gamma integration
or prime integration in Lebesgue $dx$.
Put

$$
\kappa(t)=t\psi(t)=\frac{t e^{-t/2}}{1-e^{-2t}},\qquad
\kappa(0)=1/2.
$$

On a single cell, algebraically factor
$b_i(y)-b_i(x)=(y-x)Q_i(x,y)$ with rational regular $Q_i$. Then

$$
\psi(y-x)[b_i(y)-b_i(x)][b_j(y)-b_j(x)]
=(y-x)\kappa(y-x)Q_i(x,y)Q_j(x,y). \tag{SD}
$$

The apparent singularity is removable. A triangular change of variables
maps the ordered same-cell region to a unit square with bounded analytic
integrand.

For adjacent cells meeting at $z$ with lengths $A,B_*>0$, set
$x=z-s,y=z+t$, $0\le s\le A$, $0\le t\le B_*$.
The jump difference need not vanish at $(s,t)=0$. Split this rectangle
along its normalized diagonal and use

$$
(s,t)=(Au,B_*uv),\qquad(s,t)=(Auv,B_*u),\quad 0\le u,v\le1.
$$

Both Jacobians are $AB_*u$. Their kernel-times-Jacobian factors become

$$
\frac{AB_*\kappa(u(A+B_*v))}{A+B_*v},\qquad
\frac{AB_*\kappa(u(Av+B_*))}{Av+B_*}. \tag{JC}
$$

They are bounded and holomorphic on a sufficiently small complex
neighborhood of the real square; the left and right rational branches
retain the jump difference. Nonadjacent cells have positive separation.
This transformation pays the jump corner without assuming continuity or
deleting any Gamma diagonal strip. Unequal cell lengths may force small
analytic neighborhoods and supply no favorable operation count.

Do not evaluate $\kappa$ through unresolved $0/0$ interval arithmetic.
For example, with entire $E(z)=\sum_{k\ge0}z^k/(k+1)!$,
$\kappa(t)=e^{-t/2}/(2E(-2t))$. Equivalently,
$\kappa(t)=e^{t/2}/(2\operatorname{sinc}(it))$ where
$\operatorname{sinc}(z)=\sin z/z$, $\operatorname{sinc}(0)=1$.
Nonfinite enclosures still require subdivision or rejection; a removable
analytic singularity is not a guarantee that a coarse interval evaluates
tightly.

### Uniform two-dimensional enclosure and theta callbacks

For a transformed $F$ bounded by $M$ on a product of affinely rescaled
Bernstein ellipses with parameters $r,s>1$, tensor Gauss quadrature on
$[0,1]^2$ has error at most

$$
\frac M2[e_n(r)+e_m(s)]. \tag{TQ}
$$

Apply the cited one-dimensional error bound one coordinate at a time; each rescaled Gauss rule has
positive weights summing to one. This standard tensor application is not
a new quadrature theorem. An adaptively calculated inner integral is
not automatically a certified holomorphic outer callback: use (TQ),
parameter-uniform inner enclosures, or interval box integration instead.
For a bounded continuous interval extension, the fallback
$\int_QF\in |Q|[F(Q)]$ is a directed enclosure after (SD)/(JC).
In the analytic callback use polarized products of real branch functions,
not complex absolute squares.

The original theta series, not an asymptotic replacement, is

$$
\Phi(z)=\sum_{n\ge1}(4\pi^2n^4e^{9z/2}-6\pi n^2e^{5z/2})
 e^{-\pi n^2e^{2z}}.
$$

For $a\le\Re z\le b$, $|\Im z|\le v<\pi/4$, let
$\lambda=\pi e^{2a}\cos(2v)>0$. After $P$ terms, a uniform modulus
remainder is at most

$$
4\pi^2e^{9b/2}U_4+6\pi e^{5b/2}U_2,\qquad
U_r=\frac{(P+1)^r e^{-\lambda(P+1)^2}}{1-\theta_r},\quad
\theta_r=\left(1+\frac1{P+1}\right)^r e^{-\lambda(2P+3)}<1. \tag{TH}
$$

The successive term ratio decreases, giving the geometric majorant.
This bounds the actual callback's omitted theta summands. It is not a
certificate for a callback whose complex box violates the strip or ratio
condition. Reflection using evenness can improve negative-real panels.

For each retained prime term, split at the original breakpoints and those
shifted by $-\log n$, integrating on $K\cup(K-\log n)$. Its pieces are
analytic and nonsingular. Endpoints, $\delta$, $\log n$ and the centers
must have rigorous enclosures; floating sorting of nearly coincident
breakpoints is not a certificate.

### Simultaneous Gamma and all-prime omitted-tail bounds

Reuse the [original-series spatial and integral majorants](../Analytic/romik2021orthogonal.md),
$\Phi(x)\le A_\Phi e^{-b_\Phi e^{2|x|}}$ with
$A_\Phi=144/5$, $b_\Phi=3/2$. The cited integral bound is

$$
\mathcal T(H)=\int_{|y|>H}\Phi(y)dy
\le\frac{96}{5}e^{-2H}e^{-(3/2)e^{2H}}.
$$

For a nonnegative multiplier $f$ write
$H_f=\int_K\Phi(x)f(x)B(x)B(x)^Tdx$.
Because $B=0$ outside $K$ and $\psi$ decreases,

$$
R_\Gamma=\int_K\Phi(x)B(x)B(x)^T
 \int_{|y|>H}\Phi(y)\psi(|x-y|)dy\,dx,
\quad0\preceq R_\Gamma\preceq\psi(H-S)\mathcal T(H)H_1. \tag{GT}
$$

Define the omitted prime row without speed normalization,
$a_{>N}(x)=\sum_{n>N}w_n[\Phi(x+\log n)+\Phi(x-\log n)]$.
The squared-difference bound gives $0\preceq R_p\preceq2H_{a_{>N}}$.
Using $w_n\le\log n/\sqrt n\le2/e<1$ and the decreasing Gaussian
integral bound, put

$$
\beta_\pm(x)=b_\Phi e^{\pm2x},\quad
V_N(x)=\frac{A_\Phi}{2N}
\left[\frac{e^{-\beta_+(x)N^2}}{\beta_+(x)}
      +\frac{e^{-\beta_-(x)N^2}}{\beta_-(x)}\right].
$$

Then $a_{>N}\le V_N$ and

$$
0\preceq R_p\preceq2H_{V_N}. \tag{PT}
$$

Every omitted prime power is included in the integer majorant. If
$\log(N+1)>2S$, all omitted shifted supports are disjoint, so exactly
$R_p=H_{a_{>N}}\preceq H_{V_N}$. This is a multiplication-potential
Gram matrix; it is not generally diagonal in the $b_j$ coefficient basis.
In particular

$$
D_{H,N}\preceq D\preceq D_{H,N}
 +\psi(H-S)\mathcal T(H)H_1+2H_{V_N}. \tag{DT}
$$

For a lower certificate omit only these positive energy remainders.
The upper bounds allow refinement decisions or validation against the
full energy; a negative truncated/lower matrix alone is not a full-form
negative witness.

### Pay variance and entry enclosures in the correct direction

For a rational vector $r$ approximating the full mean $\mu$, define

$$
C_r=G-\mu r^T-r\mu^T+rr^T
=\int_{\mathbb R}(B-r)(B-r)^T d\nu.
$$

Then $C_r-(G-\mu\mu^T)=(\mu-r)(\mu-r)^T$. Thus, for
$F_r=D_{H,N}-c_\varepsilon C_r$,

$$
T_\varepsilon-F_r
=R_\Gamma+R_p+c_\varepsilon(\mu-r)(\mu-r)^T\succeq0. \tag{MC}
$$

The deliberate centering loss is only quadratic in $\mu-r$.
The last term in $C_r$ is $rr^T$, not $\nu(K)rr^T$: the constant
centering vector extends outside the trial functions' compact support.

Suppose symmetric rational $\widehat F$ and symmetric nonnegative
rational upper bounds $E_{ij}$ enclose $|(F_r)_{ij}-\widehat F_{ij}|\le E_{ij}$. Set

$$
d_i=\sum_jE_{ij},\qquad L_{\rm cert}=\widehat F-\operatorname{diag}(d_i).
$$

From $2|z_i z_j|\le |z_i|^2+|z_j|^2$ for complex coefficients,

$$
L_{\rm cert}\preceq F_r\preceq T_\varepsilon. \tag{LCERT}
$$

Outward rational rounding supplies the rational error bounds.
Certified PSD of this rational lower matrix would certify the precise (MT)
condition for the prior whole-low-subspace approximation at
$\tau=\varepsilon/8$. Failed lower-matrix positivity does not establish
indefiniteness of the full target. Entrywise lower rounding is not a
substitute for (LCERT).

This is a finite assembly interface, not an assembled or signed matrix.
No numerical feasibility, threshold-uniform control, cofinal window
certificate, original general quadrature theorem, Lean, RH or full Robin
conclusion is supplied. Existing source methods are reused; the new
work is their same-object transfer with correct jumps, tails and variance.
