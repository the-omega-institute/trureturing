---
bibkey: ehm2024grammatrices
authors: Werner Ehm
year: 2024
title: On certain Gram matrices and their associated series
doi: null
url: https://arxiv.org/abs/2405.06349v2
claim: "Theorem 2.1 and Proposition 3.1 give full-space fractional-part Gram kernels; Section 8 separates moment products from a signed inversion error, and Proposition 8.1 centers moments by modifying the Selberg coefficients. The known modification has a paid comparison with the actual balanced residual, but no complete residual estimate is supplied."
strata_touched: []
license: citation-only
triage: anchor
---

# Fractional-part Gram kernels and known moment centering

The pinned source is [arXiv:2405.06349v2](https://arxiv.org/html/2405.06349v2),
revised 13 May 2024. The selected statements and the argument of
Proposition 8.1 were inspected. No independent whole-paper proof audit,
Lean certification or originality claim is made. The citation records
the author version without asserting a journal DOI.

## Existing kernels and their remaining signed term

For $u,v>0$, Theorem 2.1, equation (9), states

$$
G^{(1)}_{u,v}=\frac1v\left(K+\frac12\log\frac vu\right)
+\frac1uS_1(v/u),\qquad K=\frac{\log(2\pi)-\gamma+1}{2},
$$

where $S_1(x)=\sum_{k\ge1}R_1(kx)$ and
$R_1(x)=\log x+\gamma-H(x)-(\{x\}-1/2)/x$.
Here $H(x)=\sum_{n\le x}1/n$. Proposition 2.1 supplies the decay
$R_1(x)=O(x^{-2})$, and hence $S_1(x)=O(x^{-2})$, at infinity.
The paper explicitly identifies the $q=1$ kernel with
Báez-Duarte–Balazard–Landreau–Saias, Proposition 90, rather than
claiming this underlying kernel as new.

Proposition 3.1, equation (18), gives

$$
G^{(1)}_{u,v}=\frac1{uv}\int_0^\infty\{tu\}\{tv\}\frac{dt}{t^2}
=\int_0^\infty\{t/u\}\{t/v\}\frac{dt}{t^2}.
$$

The second equality is the substitution by $uv$ and symmetry of the
two factors. Thus $u=n,v=k$ matches the full Gram kernel for the
fractional-part probes in the
[actual Selberg residual](corvalan2023interpolation.md). It is not
the truncated, weighted step kernel on $N\le m\le N^2$.

Section 8.1, equation (50), already decomposes the full quadratic form.
For arbitrary finite real coefficients $a_n$, write
$L_j=\sum_{n\le N}a_n\log^j(n)/n$ and
$M_j=\sum_{n\le N}a_n\log^j(n)$. Then

$$
\begin{aligned}
Q_{a,N}^{(1)}
&=M_0\left(KL_0+\frac{L_1+1}{2}\right)-\frac{M_1L_0}{2}
 +(\gamma-1)L_0-L_1+\mathfrak E_{a,N}^{(1)},\\
\mathfrak E_{a,N}^{(1)}
&=\sum_{m\le N}\frac{a_m}{m}
\left(\sum_{n\le N}a_nS_1(n/m)-R_1(1/m)\right).
\end{aligned}
$$

The paper calls estimating this inversion error a major challenge
and sets it aside in that discussion. Convergence of the centered
$L_j$ factors alone does not control their products with $M_j$;
the source states this limitation explicitly. The inversion error
is signed, and is not the project's nonnegative local energy $E_N$.
These formulas are existing decompositions, not a supplied upper
bound for the complete quadratic residual.

## The source's coefficient modification

Section 8.2, equation (53), uses the known coefficients

$$
\nu_{n,N}=\mu(n)\left(1-\frac{\log n}{L}
-\frac{A\log n+B}{nL}\right)-\frac{C}{nL},\qquad L=\log N.
$$

Proposition 8.1 is conditional on fixed real $A,B,C$ solving the
specified system. With
$\eta_j=(-1)^j(1/\zeta)^{(j)}(2)$, that system is

$$
\begin{aligned}
A\eta_1+B\eta_0+C\zeta(2)&=1,\\
A\eta_2+B\eta_1-C\zeta'(2)&=2\gamma,\\
A\eta_3+B\eta_2+C\zeta''(2)&=6(\gamma^2+\gamma_1).
\end{aligned}
$$

Here $\gamma_1$ is the Stieltjes constant. Under this condition,
equations (54)–(55) match the modified centered moments with the
source's differences of rescaled Möbius moments, up to
$O(N^{-1}\log^jN)$ and $O(\log^jN)$, respectively, for $j=0,1,2$.
Each source difference has the form $\Delta X_j=X_j-X_{j+1}/L$;
the $L$ moments are centered at their stated limits before taking
this difference. This moment matching does not assert that the
complete-period Fourier mean $d_N$ vanishes. The construction and
its centering property are reused from the paper. They do not bound
its inversion error or the complete approximation norm.

## Paid comparison with the balanced residual

There is a simple application to the exact balanced dictionary of the
[Selberg note](corvalan2023interpolation.md), without using a full-space
Gram formula as a truncated kernel. For any fixed real $A,B,C$, let
$a_{N,n}=\mu(n)\log(N/n)/L$ as there, and put

$$
\Delta_{N,n}=\nu_{n,N}-a_{N,n}
=-\frac{\mu(n)(A\log n+B)+C}{nL}.
$$

This comparison does not require solving the centering system. On the
same dictionary $b_n=\{1/(nx)\}-\{1/x\}/n$, let
$v_N=-\sum_{2\le n\le N}a_{N,n}b_n$ and
$\widetilde v_N=-\sum_{2\le n\le N}\nu_{n,N}b_n$.
For $m\ge N$ their step residuals differ by
$\sum_{n\le N}\Delta_{N,n}\{m/n\}$. Consequently

$$
\sup_{m\ge N}|\widetilde R_N(m)-R_N(m)|
\le\frac1L\sum_{n\le N}\frac{|A|\log n+|B|+|C|}{n}
\ll_{A,B,C} L\qquad(N\ge3).
$$

Use the actual telescoping weight
$\sum_{m=N}^{N^2}1/[m(m+1)]\le1/N$. If $\widetilde E_N$ is the
same local energy with the modified coefficients, then

$$
\left|\sqrt{\widetilde E_N}-\sqrt{E_N}\right|
\ll_{A,B,C}\frac{\log N}{\sqrt N}.
$$

The global comparison is also paid. For
$\rho_n(x)=\{1/(nx)\}$ on the half-line, scaling gives
$\|\rho_n\|_2=n^{-1/2}\|\rho_1\|_2$, and
$\|b_n\|_2\le2n^{-1/2}\|\rho_1\|_2$. Hence

$$
\|\widetilde v_N-v_N\|_{L^2(0,1)}
\le\frac{2\|\rho_1\|_2}{L}
\sum_{n\ge2}\frac{|A|\log n+|B|+|C|}{n^{3/2}}
\ll_{A,B,C}\frac1{\log N}.
$$

Thus a genuinely supplied complete bound for the modified family can
be compared with the original one, with these independent allowances.
The allowances themselves supply no such bound. These are paper
applications of elementary norm and harmonic estimates, not new
supplier theorems or Lean-certified statements.

The modified family is not silently substituted into the original
Fourier formulas. For example, when $C\ne0$ the additional
$-C/(nL)$ term can give non-squarefree denominators nonzero aliases.
The general alias formula still applies, but the original squarefree
support and short logarithmic Möbius formula must be recalculated.
Nor do these norm comparisons supply a same-integer signed Robin
budget, a FIB approximation rate or a proof of RH.
