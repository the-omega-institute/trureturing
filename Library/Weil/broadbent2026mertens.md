---
bibkey: broadbent2026mertens
authors: Samuel Broadbent, Andrew Fiori, Habiba Kadiri, Nathan Ng, Kirsten Wilk
year: 2026
title: Bounds for Mertens sums
doi: null
url: https://arxiv.org/abs/2608.01498v1
claim: Weighted Mertens estimates supply a finite error moment for the higher-prime-power part of the Weil form; its smooth autocorrelation application retains a rank-one term, a scalar correction and a derivative-norm remainder, without a sign bound for the remaining prime contribution.
strata_touched: []
license: citation-only
triage: anchor
---

# Weighted Mertens input and the Weil prime-power budget

This is a paper-level application of classical weighted Mertens asymptotics and existing effective estimates. It is not a new prime-distribution theorem, a priority claim, or a compiled Lean result. The primary statements and the indicated constants were inspected on 1 October 2026; neither preprint's complete proofs or table-generating computations were independently rerun.

## Exact source and error moment

[Broadbent–Fiori–Kadiri–Ng–Wilk, arXiv:2608.01498v1](https://arxiv.org/pdf/2608.01498v1), printed pp.1–2, equations (2) and (6), identify

$$
\Upsilon(x)=\sum_{p\le x}\frac{\log p}{p}=\log x-M'+o(1),\qquad
M'=\gamma+\sum_p\frac{\log p}{p(p-1)}.
$$

For $v\ge0$ put

$$
A(v)=\Upsilon(e^v),\quad B=-M',\quad E(v)=A(v)-v-B,\quad
M_1=\int_0^\infty v|E(v)|\,dv.
$$

Theorem 3(ii), equation (18), printed p.4, and Table 5, printed p.42, give

$$
|E(v)|\le\frac{1.4891}{v^3}\quad(v\ge20),\qquad
\int_{20}^\infty v|E(v)|\,dv\le0.074455.
$$

Thus the required moment is supplied directly by an existing Mertens bound. For an explicit coarse finite-interval bound, $0<M'<5$: use $0<\gamma<1$, $\log n\le\sqrt n$, and $\sum_{n\ge2}n^{-3/2}<2$. Also $A(v)\le v(1+v)$ by harmonic-sum comparison, so $|E(v)|\le v^2+2v+5$. Consequently, using the external Table 5 constant,

$$
M_1\le\frac{139000}{3}+\frac{14891}{200000}<46334.
$$

Theorem 3(i)'s printed exponential rate $0.8746$ differs from the $C\approx0.84768$ used in its proof; its prefactor $9.2203$ also differs from equation (150)'s $9.2204$. Neither exponential version is used here.

An alternative explicit supplier, independent of that Table 5 value, is [Fiori–Jaskari, arXiv:2609.23222v1](https://arxiv.org/pdf/2609.23222v1). Theorem 1.1, printed p.3, applies for $x\ge x_0\ge e^3$; Table 1, printed p.4, gives $L(e^3)=0.2390$. With

$$
D=\frac52\left(\frac53\right)^{1/5}\left(\frac{2000}{161967}\right)^{3/5},
$$

its estimate implies $e^{-v}|\psi(e^v)-e^v|\le0.239e^{-D\sqrt v}$ for $v\ge3$: use $\log v\le\sqrt v$ and $1+\log\log v/(15\log v)\ge1$. For $\Delta(v)=e^{-v}\vartheta(e^v)-1$, the elementary higher-power comparison gives

$$
|\Delta(v)|\le0.239e^{-D\sqrt v}+\frac{v^2}{2\log2}e^{-v/2}\quad(v\ge3),
\qquad |\Delta(v)|\le1+v\quad(0\le v\le3).
$$

Equation (137) of the Mertens source, extended below $\log2$ by partial summation, is

$$
E(v)=\Delta(v)-\int_v^\infty\Delta(w)\,dw.
$$

Tonelli therefore yields the alternative budget

$$
M_1\le\int_0^\infty(v+v^2/2)|\Delta(v)|\,dv
\le\frac{225}{8}+\frac{239}{1000}\left(\frac{12}{D^4}+\frac{120}{D^6}\right)+\frac{240}{\log2}<500000.
$$

For the last comparison, $D>99/500$ follows by an exact rational fifth-power comparison, and $\log2>1/2$ suffices. This alternative still uses the Fiori–Jaskari theorem and its Table 1 constant as external inputs. It does not certify either source's computations. The weaker $\vartheta(x)=x+O(x/\log^2x)$ row in the [Dusart note](dusart2010estimates.md) alone does not supply this weighted moment.

## Application to every compact smooth test

Let $g\in C_c^\infty(\mathbb R;\mathbb C)$, without an evenness, normalization or nonnegativity assumption. Set

$$
R_g(t)=\Re\int g(x)\overline{g(x-t)}\,dx,\qquad
T(g)=2\sum_{p}\sum_{k\ge2}\log p\,p^{-k/2}R_g(k\log p),
$$

$$
\kappa=-\gamma+\sum_p\frac{\log p}{\sqrt p(p-1)},\qquad
D_3=\sum_p\sum_{k\ge3}k^2(\log p)^3p^{-k/2}.
$$

The sum defining $T(g)$ has finitely many nonzero terms by compact support. The series defining $\kappa$ and $D_3$ converge absolutely. The common-test estimate is

$$
\boxed{\left|T(g)-\frac12\left|\int g\right|^2-2\kappa\|g\|_2^2\right|
\le(8M_1+D_3)\|g'\|_2^2.} \tag{1}
$$

Here is a complete paper derivation. The real autocorrelation is even, with

$$
R_g(0)=\|g\|_2^2,\quad R_g'(0)=0,\quad
\int_0^\infty R_g(t)dt=\tfrac12|\int g|^2,\quad
|R_g''(t)|\le\|g'\|_2^2.
$$

The last inequality follows by integration by parts and Cauchy–Schwarz. Thus $|R_g'(t)|\le|t|\|g'\|_2^2$ and $|R_g(t)-R_g(0)|\le t^2\|g'\|_2^2/2$.

For the square contribution, Stieltjes integration from $v=0$ gives the exact identity

$$
T_2(g)=2\int_0^\infty R_g(2v)dA(v)
=\tfrac12|\int g|^2+2B\|g\|_2^2-4\int_0^\infty E(v)R_g'(2v)dv.
$$

Since $A(0)=0$ and $E(0)=-B$, there is no omitted prime-2 endpoint correction. The last remainder term, including its factor $-4$, has absolute value at most $8M_1\|g'\|_2^2$. For $k\ge3$, the quadratic autocorrelation bound gives

$$
\left|T_{\ge3}(g)-2C_{\ge3}\|g\|_2^2\right|\le D_3\|g'\|_2^2,\qquad
C_{\ge3}=\sum_p\frac{\log p}{p^{3/2}(1-p^{-1/2})}.
$$

Primewise geometric summation shows $B+C_{\ge3}=\kappa$, proving (1). No pointwise positivity of $R_g$ is used; for complex or sign-changing tests it can be negative.

For a simple explicit constant, $r=p^{-1/2}<3/4$ gives $\sum_{k\ge3}k^2r^k\le192r^3$. Comparison on each $[n-1,n]$ gives

$$
\sum_{n\ge2}\frac{(\log n)^3}{n^{3/2}}
\le\int_1^\infty\frac{(\log x+\log2)^3}{x^{3/2}}dx
=96+48\log2+12(\log2)^2+2(\log2)^3<158.
$$

Hence $D_3<30336$. With the alternative $M_1<500000$ supplier one may use $4040000$ in place of $8M_1+D_3$. This constant is deliberately coarse. The sharper Table 5 route is not needed for it.

For fixed $h\in C_c^\infty(\mathbb R;\mathbb C)$ with $\|h\|_2=1$ and $f_R(x)=R^{-1/2}h(x/R)$, (1) specializes to

$$
T(f_R)=\frac R2|\int h|^2+2\kappa+\epsilon_R,\qquad
|\epsilon_R|\le\frac{(8M_1+D_3)\|h'\|_2^2}{R^2}.
$$

Mean zero removes the linear term, not the constant. The square part alone then tends to $2B<0$. For the combined constant, primes 2 and 3 already give $\kappa>1/36$, using $\log2>2/3$, $\log3>1$, $\sqrt2<3/2$, $\sqrt3<2$ and $\gamma<2/3$.

## Reuse and remaining boundary

The project's [Mertens estimates](../../D5/S3/Weil/Mertens/Estimates.lean) already supply the correction-series summability and a bounded first-Mertens error. Its [log-zeta source](../../D5/S3/Weil/Mertens/LogZeta.lean) contains a private general logarithmic-moment summability lemma. Mathlib supplies prime-power reindexing and the $-\gamma$ finite part of $-\zeta'/\zeta$ at $s=1$, after subtracting $1/(s-1)$. These are reusable inputs, not new declarations to wrap. The inspected bounded first-Mertens statement alone does not identify $B$ or prove $M_1<\infty$; the external suppliers above fill those paper-level premises.

The [earlier triangular-kernel account](../../docs/develop/theory/QUANTUM-RH.md) already treats a prime-square correction with a different kernel and scaling. Equation (1) specifies the current smooth autocorrelation, norm and uniformity; no priority claim follows from changing that formulation.

In the full Weil form the contribution is $-T(g)$. Omitting higher prime powers on the ground that their ordinary counting mass is $o(X)$ therefore loses the displayed linear and scalar terms in this normalization. Equation (1) is uniform in support and coefficients with its **derivative-norm** weight; it is not an estimate in the weaker logarithmic Weil form norm. It supplies no sign bound for the remaining primary-prime/continuum discrepancy. The [actual localization residual](frankliebseiringer2006hardy.md) retains that separate obligation. No all-support positivity, Robin inequality or RH conclusion has been established here.
