---
bibkey: gonek1985landau
authors: Steven M. Gonek
year: 1985
title: A Formula of Landau and Mean Values of ζ(s)
doi: null
url: https://www.sas.rochester.edu/mth/people/faculty/gonek-steve/assets/pdf/8-landau-form.pdf
claim: The unconditional uniform Landau formula retains actual complex zeros; its pointwise prime-power main term vanishes in the prescribed continuum pairing, and absolute transfer of its published errors does not supply the missing signed middle bound.
strata_touched: []
license: citation-only
triage: anchor
---

# Uniform Landau sums and the original dilation test

The primary source is the [author-hosted scan](https://www.sas.rochester.edu/mth/people/faculty/gonek-steve/assets/pdf/8-landau-form.pdf), *Topics in Analytic Number Theory* (1985). Theorem 1, equation (3), and the definition following it were inspected on printed pp.92–93. The theorem is unconditional. Theorem 2 on p.93 explicitly assumes RH and is not an unconditional supplier here. The applications below are paper-level, without a Lean implementation.

## Preserve the source's arithmetic variable

For actual nontrivial zeros $\rho=\beta+i\gamma$, counted with their analytic multiplicities, set

$$
L_V(x)=\sum_{0<\gamma\le V}m_\rho x^\rho,
\qquad x,V>1.
$$

The source sums over zeros with repetition; $m_\rho$ makes that convention explicit. Its real-variable function $\Lambda(x)$ equals $\log p$ at an exact prime power $x=p^k$ and zero at every other real $x$. Write $\langle x\rangle$ for the distance to the nearest prime power other than $x$ itself. Theorem 1 supplies the uniform formula

$$
\begin{aligned}
L_V(x)={}&-\frac{V}{2\pi}\Lambda(x)
+O\!\left(x\log(2x)\log\log(3x)\right)
+O\!\left(x\log(2V)\right)\\
&+O\!\left(\log x\min\!\left(V,\frac{x}{\langle x\rangle}\right)\right)
+O\!\left(\min\!\left(\frac{\log V}{\log x},V\log V\right)\right).
\end{aligned} \tag{1}
$$

In particular the nearest-prime-power and near-$1$ errors must be retained. A formula only for fixed $x$ or for integer $x$ does not supply a uniform continuum pairing on a growing interval. No replacement of $x^\rho$ by $\sqrt x\,x^{i\gamma}$ is made.

## Exact map of the existing test

Use the unchanged $\phi,\Phi,w,b,p$ of [the research volume, §§19.3 and 30](../../docs/develop/theory/RH_RESEARCH_LANE_THEORY.md), with $\Phi(z)=\int\phi(t)e^{-izt}dt$, $b=2+\sqrt5$, and $p(z)=z^2(1+4z^2)^2$. To avoid confusing a zero height with a test kernel, write

$$
K=\phi*\phi,\qquad
J(v)=\int_1^b\frac{w(u)}uK(v/u)\,du,
\qquad J_R(t)=R^{-1}J(t/R).
$$

Thus $J$ is exactly the volume's $\bar K$, rather than a new kernel. It is smooth, real, even, supported exactly on $[-b,b]$, flat at the endpoints and positive in the interior. Define the differential test

$$
\begin{aligned}
h_R&=-D_t^2(1-4D_t^2)^2J_R\\
&=-R^{-3}J''(t/R)+8R^{-5}J^{(4)}(t/R)-16R^{-7}J^{(6)}(t/R).
\end{aligned}
$$

The ordinary Fourier multiplier calculation gives

$$
\widehat h_R(z)=p(z)\int_1^bw(u)\Phi(uRz)^2\,du. \tag{2}
$$

This is the original analytic square, including its annihilation at $z=0,\pm i/2$. For $T\ge H$ and $z_\rho=\gamma-i(\beta-1/2)$, the original moving middle therefore has the exact finite-sum representation

$$
\begin{aligned}
B_{H,T}(R)
&=2\sum_{H<\gamma\le T}m_\rho\widehat h_R(z_\rho)\\
&=4\Re\int_0^{bR}h_R(t)e^{-t/2}
\bigl(L_T(e^t)-L_H(e^t)\bigr)\,dt. \tag{3}
\end{aligned}
$$

Indeed $iz_\rho=\rho-1/2$; evenness permits either Fourier sign. Reflection $\rho\mapsto1-\overline\rho$ preserves positive ordinate, multiplicity and both height cutoffs. It gives

$$
e^{t/2}L_V(e^{-t})=\overline{e^{-t/2}L_V(e^t)},
$$

which accounts for the second factor of two. No critical-line hypothesis enters (2)–(3). At a cutoff equal to a zero ordinate, all its multiplicity belongs to the inclusive head. These are applications of Fourier calculus and the existing zeta symmetries, not a new explicit formula.

## What survives continuum integration

The pointwise main term in (1) is supported on the countable set $t=\log(p^k)$. Hence its ordinary integral against $h_R(t)e^{-t/2}$ is zero. That function is not the prime measure $\sum_{n\ge2}\Lambda(n)\delta(t-\log n)$. Turning it into that measure would change the source theorem.

With the actual remainder $\mathcal E_V(x)=L_V(x)+V\Lambda(x)/(2\pi)$, (3) is precisely

$$
B_{H,T}(R)=4\Re\int_0^{bR}h_R(t)e^{-t/2}
\bigl(\mathcal E_T(e^t)-\mathcal E_H(e^t)\bigr)\,dt. \tag{4}
$$

Thus the displayed negative main term has no signed contribution to this particular pairing. Any useful cancellation must remain in (4), including the prime neighborhoods represented by the error terms.

For the moving height $T=250000R$, the map is $x=e^t$ with $0<t<bR$. On every fixed interior band $t=vR$, $x$ is exponential in $R$ while $T$ is linear. The second error in (1), after the half weight and absolute integration, contains the allowance

$$
\log(2T)\,\mathcal A(R),\qquad
\mathcal A(R)=\int_0^{bR}|h_R(t)|e^{t/2}dt.
$$

Its exact exponential rate follows by the standard endpoint Laplace estimate:

$$
\lim_{R\to\infty}\frac{\log\mathcal A(R)}R=\frac b2. \tag{5}
$$

For completeness, bounded derivatives give $\mathcal A(R)\le CR^{-2}e^{bR/2}$. In every interval $(b-\varepsilon,b)$, $J''$ is nonzero somewhere: otherwise $J$ would be affine there and its endpoint flatness would contradict interior positivity. Choose a fixed closed subinterval $[a,c]$ there with $|J''|\ge\delta>0$. Uniformly on that subinterval, $|h_R(Rv)|\ge\delta/(2R^3)$ for all sufficiently large $R$, giving

$$
\mathcal A(R)\ge\frac{\delta(c-a)}{2R^2}e^{aR/2}.
$$

Letting $\varepsilon$ decrease gives (5). This applies an ordinary Laplace principle to the already fixed test; it is not a new zero estimate.

Consequently the absolute allowance supplied by this transfer has exponential rate $b/2$, rather than a decaying rate. It cannot pay the existing guaranteed reserve $e^{-120R}$. This is a limitation of the theorem together with this absolute-error transfer, not a lower bound on the actual error or a sign assertion about $B_{H,T}$. Signed integration of the full remainder remains unresolved. The [existing half-weighted discrepancy note](chirrehelfgott2025nonnegative.md) records the corresponding arithmetic pairing; repeating its explicit formula does not supply the missing comparison.
