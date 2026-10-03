---
bibkey: broadbent2026mertens
authors: Samuel Broadbent, Andrew Fiori, Habiba Kadiri, Nathan Ng, Kirsten Wilk
year: 2026
title: Bounds for Mertens sums
doi: null
url: https://arxiv.org/abs/2608.01498v1
claim: Weighted Mertens estimates supply the higher-prime-power derivative budget. A separate paper application of the entire-xi Hadamard expansion gives an upper budget in the actual shifted Gamma energy, retaining the pole term and an actual-zero contribution; the primary-prime comparison remains unresolved.
strata_touched: []
license: citation-only
triage: anchor
---

# Weighted Mertens input and the Weil prime-power budget

This is a paper-level application of classical weighted Mertens asymptotics and existing effective estimates. It is not a new prime-distribution theorem, a priority claim, or a compiled Lean result. The Mertens and prime-counting statements and their indicated constants were inspected on 1 October 2026; neither preprint's complete proofs or table-generating computations were independently rerun.

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

The higher-power remainder has a definite sign. Write $\tau_tg(x)=g(x-t)$. The identity $2(R_g(0)-R_g(t))=\|g-\tau_tg\|_2^2$ gives

$$
T_{\ge3}(g)-2C_{\ge3}\|g\|_2^2=-\mathcal D_{\ge3}(g),\qquad
\mathcal D_{\ge3}(g)=\sum_p\sum_{k\ge3}\log p\,p^{-k/2}\|g-\tau_{k\log p}g\|_2^2\ge0.
$$

This energy sum generally has infinitely many nonzero terms but converges absolutely, even though the correlation sum $T(g)$ is finite; its convergent constant part supplies the tail. It satisfies $\mathcal D_{\ge3}(g)\le D_3\|g'\|_2^2$. Hence the error $\epsilon(g)=T(g)-\tfrac12|\int g|^2-2\kappa\|g\|_2^2$ has the sharper asymmetric bound

$$
-(8M_1+D_3)\|g'\|_2^2\le\epsilon(g)\le8M_1\|g'\|_2^2. \tag{2}
$$

In the full form, $-\epsilon(g)=4\int_0^\infty E(v)R_g'(2v)dv+\mathcal D_{\ge3}(g)$. The energy is an independently nonnegative contribution; the remaining integral keeps its unknown sign.

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

In the full Weil form the contribution is $-T(g)$. Omitting higher prime powers on the ground that their ordinary counting mass is $o(X)$ therefore loses the displayed linear and scalar terms in this normalization. Equation (1) is uniform in support and coefficients with its **derivative-norm** weight. The complementary logarithmic budget below uses a different supplier. Neither supplies a sign bound for the remaining primary-prime/continuum discrepancy. The [actual localization residual](frankliebseiringer2006hardy.md) retains that separate obligation. No all-support positivity, Robin inequality or RH conclusion has been established here.

## An upper budget in the actual logarithmic Gamma energy

Keep every definition of the same compact smooth complex $g$ above. The following is a paper application of classical Hadamard and Gamma identities, with their specific boundary pairing made explicit. It is not a new Hadamard theorem, a priority claim, or a Lean-verified estimate. In particular the Mertens derivative estimate is reused rather than proved again.

Fix the angular Fourier convention

$$
\widehat g(\tau)=\int_{\mathbb R}g(x)e^{-i\tau x}dx,
\qquad \|g\|_2^2=\frac1{2\pi}\int_{\mathbb R}|\widehat g(\tau)|^2d\tau.
$$

Write $\Psi=\Gamma'/\Gamma$ for digamma and use the **entire** function

$$
\xi(s)=\tfrac12s(s-1)\pi^{-s/2}\Gamma(s/2)\zeta(s),
\qquad
c_1=\frac{\xi'}{\xi}(1)=1+\frac\gamma2-\log2-\frac12\log\pi.
$$

The removable value at one is understood. This is not the meromorphic completion $\pi^{-s/2}\Gamma(s/2)\zeta(s)$ used in the project's [XiLogDeriv](../../D5/S3/Weil/ZetaExplicit/XiLogDeriv.lean). The [entire reading](../../D5/S3/Zeros/CompletedZeta.lean) has the appropriate pole removal, but its existing declarations alone do not supply the global Hadamard expansion used here.

The source for that expansion is [Lagarias, arXiv:math/0404394v4](https://arxiv.org/pdf/math/0404394v4): the paragraph before Theorem 2.1 identifies $\xi(s,\pi_{\rm triv})=2\xi(s)$; Theorem 2.1(3), (4), (6), printed p.7, supplies the strict zero strip, counting estimate and order one; Lemma 4.1's proof, printed p.14, supplies the Hadamard product and cancellation of its linear coefficient by the starred reciprocal-zero sum. The factor two leaves the logarithmic derivative unchanged. The inspected PDF has SHA-256 `86f3d3c49f5a889f121bb1f04f67694cb9066dc8360f6988165788679594a4a7`. These classical results are cited, not reproved or independently certified here.

The direct positive-logarithmic-derivative supplier is [Matiyasevich–Saidak–Zvengrowski, *Horizontal Monotonicity of the Modulus of the Riemann Zeta Function and Related Functions*, arXiv:1205.2773v1](https://arxiv.org/pdf/1205.2773v1), §2, the proof of Theorem 1.1, printed p.4. It displays the conjugate-paired Hadamard logarithmic-derivative series and its positive real summands to the right of all zeros. Its definition on printed p.2 is $(s-1)\Gamma(1+s/2)\pi^{-s/2}\zeta(s)$, equal to the entire $\xi$ above by Gamma recurrence. Its $\xi$ calculation has no height restriction; the height restrictions for its later $\zeta$ and $\eta$ comparisons are not used. This known positivity is reused, not claimed as a new result.

Taking real parts of that expansion gives, for $1\le\sigma\le2$,

$$
\Re\frac{\xi'}{\xi}(\sigma+2i\tau)
=\sum_{\rho=\beta+i\gamma_\rho}
\frac{\sigma-\beta}{(\sigma-\beta)^2+(2\tau-\gamma_\rho)^2}. \tag{3}
$$

Every zero is counted with its actual multiplicity. The real series is absolutely convergent; the strict strip $0<\beta<1$ makes each term positive. This uses no RH. The zero-counting estimate also gives $\sum_\rho(1+\gamma_\rho^2)^{-1}<\infty$.

### The actual even-power boundary pairing

Let $h(\tau)=|\widehat g(\tau)|^2$, a nonnegative Schwartz function, and put

$$
F(s)=-\frac{\zeta'}{\zeta}(s)-\frac1{s-1},\qquad F(1)=-\gamma.
$$

For $0<\delta\le1$, absolute convergence in $\Re s>1$ and Parseval give

$$
2\sum_p\sum_{j\ge1}\log p\,p^{-j(1+\delta)}R_g(2j\log p)
=\frac1{2\pi}\int_{\mathbb R}
2\Re\left(-\frac{\zeta'}{\zeta}(1+\delta+2i\tau)\right)h(\tau)d\tau. \tag{4}
$$

The left side has finitely many nonzero correlations, so its limit is the actual sum of every even prime power. No ordinarily convergent undamped Dirichlet series on $\Re s=1$ is asserted.

The regular-part pairing on the right also converges to its stated boundary value. Here is the needed uniform justification, which does not require a quantitative zero-free region. For $0<a\le2$ and a real ordinate $u$,

$$
\int_{\mathbb R}\frac{a}{a^2+(2\tau-u)^2}h(\tau)d\tau
\le\frac{C_h}{1+u^2}, \tag{5}
$$

where $C_h$ depends only on $h$. For $|u|\ge2$, split at $|2\tau|=|u|/2$. On the first region the kernel is at most $8/u^2$; on the second, $h\le16\sup_\tau(1+\tau^2)h(\tau)/(1+u^2)$ and the full kernel integral is $\pi/2$. For $|u|<2$ the same full integral and $\|h\|_\infty$ give a uniform bound. For each fixed zero, its width $a=1+\delta-\beta$ tends to the positive width $1-\beta$. Equation (5) and reciprocal-square zero summability therefore allow the limit through the paired sum in (3).

The identity

$$
2\Re F(s)=-2\Re\frac{\xi'}{\xi}(s)
+2\Re\frac1s-\log\pi+\Re\Psi(s/2)
$$

reduces the remaining pairing to a bounded rational term and digamma. The classical [digamma asymptotic, DLMF 5.11.2](https://dlmf.nist.gov/5.11.E2), gives logarithmic growth uniformly in $1/2\le\Re(s/2)\le1$, so Schwartz decay dominates these terms. Thus

$$
\lim_{\delta\downarrow0}\frac1{2\pi}\int 2\Re F(1+\delta+2i\tau)h(\tau)d\tau
=\frac1{2\pi}\int 2\Re F(1+2i\tau)h(\tau)d\tau. \tag{6}
$$

The pole is accounted for separately:

$$
\Re\frac1{\delta+2i\tau}=\frac{\delta}{\delta^2+4\tau^2}
\longrightarrow\frac\pi2\delta_0.
$$

Its factor two in (4), followed by $1/(2\pi)$, contributes exactly $\tfrac12|\widehat g(0)|^2$. In particular the pole is not absorbed into the regular multiplier or silently discarded.

### Positive residual accounting

The remaining odd powers have an absolutely and uniformly convergent series

$$
O(\tau)=\sum_p\sum_{\substack{k\ge3\\k\text{ odd}}}\log p\,p^{-k/2}e^{-ik\tau\log p},
\qquad C_{\rm odd}=\sum_p\frac{\log p}{\sqrt p(p-1)},
\qquad \kappa=-\gamma+C_{\rm odd}.
$$

Combining (4)–(6) with these odd powers identifies the actual residual as

$$
\epsilon(g)=\frac1{2\pi}\int m_\epsilon(\tau)h(\tau)d\tau,
\qquad
m_\epsilon=2\Re F(1+2i\tau)+2\Re O(\tau)-2\kappa. \tag{7}
$$

Use the shifted energy appearing in the full-form account,

$$
E_*(g)=\int_0^\infty\frac{e^{-5t/2}}{1-e^{-2t}}
\|g-\tau_tg\|_2^2dt,
\qquad
a_*(\tau)=\Re\Psi(5/4+i\tau/2)-\Psi(5/4).
$$

The existing [Gamma energy decomposition](../../D5/S3/Weil/ZetaGamma/ArchimedeanJumpDecomposition.lean) supplies the unshifted representation for its bundled even tests. Here its paper-level Fourier calculation is used for a general compact smooth complex $g$; Parseval and Tonelli apply to the nonnegative translation energy without an evenness restriction. The kernel difference $e^{-t/2}$ and the digamma recurrence give $a_*=a_\Gamma-16\tau^2/(1+4\tau^2)$, where $a_\Gamma=\Re\Psi(1/4+i\tau/2)-\Psi(1/4)$. The classical [duplication](https://dlmf.nist.gov/5.5.E8) and [reflection](https://dlmf.nist.gov/5.5.E4) formulas give

$$
\Re\Psi(1/2+i\tau)-\Psi(1/2)
=a_\Gamma(\tau)+\frac\pi2\left(\frac1{\cosh(\pi\tau)}-1\right).
$$

Consequently, with $S(\tau)=\Re(\xi'/\xi)(1+2i\tau)$ and

$$
d_\xi=2-\frac\pi2+2c_1
=4+\gamma-\log(4\pi)-\frac\pi2,
\qquad
j(\tau)=\frac2{1+4\tau^2}-\frac\pi{2\cosh(\pi\tau)},
$$

the exact multiplier identity is

$$
m_\epsilon=a_*+d_\xi-2S-2(C_{\rm odd}-\Re O)-j.
$$

Pairing with the same $h$ yields the paper-level decomposition

$$
\boxed{E_*(g)-\epsilon(g)+d_\xi\|g\|_2^2
=\mathcal Z(g)+\mathcal D_{\rm odd}(g)+\mathcal J(g),} \tag{8}
$$

$$
\mathcal Z(g)=\frac1{2\pi}\int 2S(\tau)h(\tau)d\tau,\qquad
\mathcal D_{\rm odd}(g)=\sum_p\sum_{\substack{k\ge3\\k\text{ odd}}}\log p\,p^{-k/2}\|g-\tau_{k\log p}g\|_2^2,
\qquad
\mathcal J(g)=\frac1{2\pi}\int j(\tau)h(\tau)d\tau.
$$

All three contributions are nonnegative and finite. For $\mathcal Z$, use (3) and (5). For the odd energy, $\mathcal D_{\rm odd}\le4C_{\rm odd}\|g\|_2^2$. For $\mathcal J$, its multiplier is bounded and nonnegative because

$$
\cosh(\pi\tau)\ge1+\frac{\pi^2\tau^2}{2}
\ge\frac\pi4+\pi\tau^2,
\qquad 2<\pi<4.
$$

Thus (8) supplies the upper budget

$$
\boxed{\epsilon(g)\le E_*(g)+d_\xi\|g\|_2^2.} \tag{9}
$$

It is uniform over all compact supports and complex coefficients. The logarithmic energy replaces the derivative expense on the upper side needed by the full form. The original two-sided derivative estimate remains useful on slow dilations and is not superseded by a two-sided logarithmic claim.

This pairing argument and its all-test application have not been compiled in Lean. The original-source Hadamard expansion and classical Gamma identities are reused inputs; the displayed accounting is a repository synthesis with no claim of worldwide novelty. No extension beyond the stated compact smooth core is asserted without an additional domain argument.
