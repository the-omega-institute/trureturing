---
bibkey: jarohsweth2020local
authors: Sven Jarohs and Tobias Weth
year: 2020
title: Local compactness and nonvanishing for weakly singular nonlocal quadratic forms
doi: 10.1016/j.na.2019.01.021
url: https://arxiv.org/abs/1811.12850v1
claim: The source supplies local compactness for the comparison kernel with singularity one over distance. An explicit cutoff estimate transports it to the minimal theta Gamma form in the actual pole measure, without requiring a fractional positive order or a density for prime jumps.
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
