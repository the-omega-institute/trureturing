---
bibkey: kaczorowski2000landau
authors: J. Kaczorowski, A. Languasco, A. Perelli
year: 2000
title: A note on Landau's formula
doi: 10.7169/facm/1538186693
url: https://www.dei.unipd.it/~languasco/lavoripdf/R12.pdf
claim: A smoothed unconditional Landau formula retains near-prime discrepancy terms and bounds the complete zero sum; its faithful transfer to the original dilation test still leaves the required signed cancellation unresolved.
strata_touched: []
license: citation-only
triage: anchor
---

# Smoothed Landau sums and the retained arithmetic remainder

The primary text is the [author's last preprint](https://www.dei.unipd.it/~languasco/lavoripdf/R12.pdf). Its title page identifies the publication as *Funct. Approx. Comment. Math.* **28** (2000), 173–186; the author's bibliography supplies [DOI 10.7169/facm/1538186693](https://doi.org/10.7169/facm/1538186693). The statements below were inspected on preprint pp.3–5. The publisher's final typeset article was not obtained, so identity of those versions is not asserted. These source applications have no Lean implementation.

## Keep the complete zero sum and the source's taper

Write

$$
\vartheta(y)=
\begin{cases}
1,&0\le y\le1/2,\\
2(1-y),&1/2<y\le1,\\
0,&y>1,
\end{cases}
\qquad
\mathcal L_V(x)=\sum_\rho m_\rho\vartheta(|\gamma|/V)x^\rho.
$$

Here $\rho=\beta+i\gamma$ ranges over all nontrivial zeros, with both ordinate signs and actual $\beta$. The multiplicity convention follows the source's residue calculation with $-\zeta'/\zeta$ in Lemma 4; no simplicity or RH hypothesis is made. This is the paper's $L(x,V)$, not its separate $R(x,V)=x-\mathcal L_V(x)$ and not a bound for the imaginary part of a positive-ordinate sum.

Corollary 1, p.4, assumes

$$
x\ge16,\qquad4\le V\le x/4,\qquad1\le M\le V/4.
$$

It decomposes the same complete sum as $\mathcal L_V=L_1+L_2+L_3$, with

$$
L_1(x,V)=-\frac1{2\pi}
\sum_{x-Mx/V<n\le x+Mx/V}(\Lambda(n)-1)H(x,V,n),
$$

$$
H(x,V,n)=\frac2V\int_{V/2}^V
\left(\int_{-\tau}^{\tau}(x/n)^{iu}du\right)d\tau.
$$

The remaining terms contain $L_2=-R_2$ plus the source's additional integer or fractional-part errors, and $L_3=-R_3$. They are not omitted in the source's total estimates. Lemma 1 gives $H(n,V,n)=3V/2$; away from $x=n$, this is an oscillatory kernel. Neither $\Lambda(n)-1$ nor the complete local contribution has a fixed sign. In particular the unsmoothed coefficient $-V\Lambda(x)/(2\pi)$ cannot be copied into this different height normalization.

Corollary 2, p.4, is unconditional and supplies

$$
|\mathcal L_V(x)|\ll\frac{x\log x}{\log(x/V)},
\qquad x\ge16,\quad4\le V\le x/4. \tag{1}
$$

The paragraph following Theorem 2, p.5, also states the unconditional consequence

$$
\int_N^{2N}|\mathcal L_V(x)|^2dx
\ll N^2\max\{N,V\log N\},
\qquad N\ge16,\quad4\le V\le N/4, \tag{2}
$$

and its analogous integer-sum bound. The paper's $\log x$ can be replaced by $\log N$ on this dyadic interval. These are published asymptotic allowances, with no explicit numerical implied constants. The more detailed Theorem 2 uses the classical Selberg integral

$$
J(N,h)=\int_{N/2}^{3N}(\psi(x+h)-\psi(x)-h)^2dx.
$$

Its additional parameter restriction is $1\le M\le\min\{N^{1/16}/(\log x)^4,V^{1/5}/(\log x)^8\}$. Thus the paragraph's stated uniform consequence (2) should not be described as a literal substitution $M=1$ into that detailed theorem at every small $V$. Nothing here strengthens a Selberg-integral or pair-correlation bound.

## Faithful taper transfer to the unchanged test

Keep exactly the $h_R$ and $\widehat h_R$ defined in the [uniform Landau note](gonek1985landau.md), and the original complete average $\bar q(R)$ in [the research volume, §§30–31](../../docs/develop/theory/RH_RESEARCH_LANE_THEORY.md). Put $T_R=250000R$ and introduce the auxiliary expression

$$
\widetilde q_R=
2\sum_{\gamma>0}m_\rho
\vartheta\bigl(\gamma/(2T_R)\bigr)\widehat h_R(z_\rho).
$$

All its weights below and at $T_R$ equal one. The complete expression is therefore retained up to a weighted part of the already bounded far tail. Direct use of the existing absolute majorant gives, for real $R\ge3$,

$$
|\bar q(R)-\widetilde q_R|
\le6000T_R^7\log T_R
e^{bR/2-\sqrt{RT_R}/3}
<\tfrac12e^{-120R}. \tag{3}
$$

Only the tail proof's strip, count and complex Fourier bound enter; no criticality assumption up to a moving unverified height is introduced. This is reuse of that proof, not additional finite zero verification. Evenness and both zeta reflections give the exact real integral

$$
\widetilde q_R=2\int_0^{bR}
h_R(t)e^{-t/2}\mathcal L_{2T_R}(e^t)\,dt. \tag{4}
$$

The all-zero normalization in (4) differs from the positive-ordinate normalization in the other note; the factor is two here. Analytic squares, actual multiplicities and all prime powers are preserved. The taper is an intermediate representation, not a replacement positivity target.

## Scope of the available total allowances

To apply (1) in (4), retain its threshold:

$$
t\ge a_R:=\log\max\{16,8T_R\}.
$$

The initial portion $0<t<a_R$ is not covered by (1) and must remain in the exact expression or receive a separate estimate. If $a_R\ge bR$, there is no eligible portion. On every fixed interior band $t=vR$ with $0<v<b$, that threshold holds for sufficiently large $R$, and

$$
\frac{t}{t-\log(2T_R)}\longrightarrow1.
$$

For sufficiently large $R$, when $a_R<bR$, the absolute allowance for the eligible portion is consequently proportional to

$$
\int_{a_R}^{bR}|h_R(t)|e^{t/2}
\frac{t}{t-\log(2T_R)}dt. \tag{5}
$$

The ratio in (5) is at least one and at most $O(\log R)$ on this portion. As $a_R=O(\log R)$, the endpoint estimate already supplied in the other note gives exponential rate $b/2$ for (5). The source's total bound therefore does not pay a decaying signed reserve, even on this eligible portion. This describes the absolute allowance, not the actual size or sign of (4).

The unconditional mean-square consequence has the same limitation. Under $x=e^t$, the pairing uses $h_R(\log x)x^{-3/2}dx$. On $[N,2N]$, Cauchy–Schwarz and (2) give

$$
\left|\int_N^{2N}h_R(\log x)x^{-3/2}\mathcal L_{2T_R}(x)dx\right|
\ll\sup_{N\le x\le2N}|h_R(\log x)|
\sqrt{\max\{N,2T_R\log N\}}.
$$

For $N=e^{vR}$, with fixed $v>0$ and $2T_R\le N/4$, the square-root factor is eventually $N^{1/2}$. This is an exponentially growing allowance multiplied by the test's polynomial scaling, rather than the needed one-sided signed estimate. It is not a lower bound on the actual integral.

## The remaining signed arithmetic object

For the same $h_R$, the ordinary half-weighted prime discrepancy is

$$
\mathcal D_R=
\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}h_R(\log n)
-\int_0^\infty h_R(t)e^{t/2}dt.
$$

Every prime power inside the actual support remains included. With $G$ and $c$ from the [existing half-weighted supplier](chirrehelfgott2025nonnegative.md), Stieltjes integration by parts is exactly

$$
\mathcal D_R=-(c-2)h_R(0)
-\int_0^\infty G(e^t)h_R'(t)dt,
\qquad G(1)=c-2.
$$

This reuses the existing discrepancy and endpoint normalization, rather than defining a new kernel or explicit formula. The smoothed Landau source improves the representation by retaining whole prime neighborhoods. Its signed local term together with all the retained errors still needs a joint estimate for the original test. Neither (1) nor (2) supplies that sign, and no equivalence with a standard Selberg-integral conjecture is asserted. The missing comparison, all-scale Weil sign, RH, Robin and FIB-to-prime intertwining remain unresolved.
