---
bibkey: chenwang2012weighted
authors: Xin Chen and Jian Wang
year: 2012
title: Weighted Poincare Inequalities for Nonlocal Dirichlet Forms
doi: null
url: https://arxiv.org/abs/1207.7140v1
claim: Theorem 5.1 controls a weaker-weight variance for the exact theta Gamma jump energy. A separate paper deduction gives zero Gamma-only gap in the pole measure and leading prime/Gamma compensation on the same normalized far-tail tests; the global joint Weil inequality remains unproved.
strata_touched: []
license: bibliographic-reference-only
triage: anchor
---

# A reusable weighted estimate for the Gamma jump energy

## Primary statement and hypotheses

The inspected source is [Chen–Wang, arXiv:1207.7140v1](https://arxiv.org/abs/1207.7140v1), submitted 31 July 2012, with its [versioned primary PDF](https://arxiv.org/pdf/1207.7140v1). Example 2.3, equation (2.30), printed p.14, defines

$$
D_{\psi,V}(h,h)=\frac12\iint |h(y)-h(x)|^2
\psi(|x-y|)e^{-V(x)}e^{-V(y)}\,dx\,dy.
$$

Here $V$ is locally bounded, $e^{-V}$ is bounded and integrable, and
$\int_0^\infty (1\wedge r^2)r^{d-1}\psi(r)\,dr<\infty$.
The ambient probability measure is

$$
d\mu_{2V}=\frac{e^{-2V(x)}\,dx}{\int e^{-2V(x)}\,dx}.
$$

Theorem 5.1, printed pp.32–33, assumes $\psi:(0,\infty)\to(0,\infty)$ is continuous. With
$\gamma(r)=\inf_{0<s\le r+1}\psi(s)$, its additional hypotheses are

$$
\int_0^1 r^{d-1}\psi(r)^{-1}\,dr<\infty,
\qquad
\int_{|x|\ge1}\frac{e^{-3V(x)}}{\gamma(|x|)}\,dx<\infty,
$$

and, for some $0<\alpha_0<1$,

$$
\int_1^\infty r^{d+\alpha_0-1}\psi(r)\,dr<\infty,
\qquad
\limsup_{|x|\to\infty}
\frac{\sup_{|z|\ge|x|}e^{-V(z)}}{\gamma(|x|)|x|^{\alpha_0}}=0.
$$

The conclusion is that there exists $C_1>0$ such that, for every real $h\in C_b^\infty(\mathbb R^d)$,

$$
\int |h-\mu_{2V}(h)|^2e^{V(x)}\gamma(|x|)\,d\mu_{2V}(x)
\le C_1D_{\psi,V}(h,h). \tag{1}
$$

The theorem does not specify a numerical value for $C_1$. Applying (1) separately to real and imaginary parts gives the same estimate for complex tests.

## Parameter map to the theta kernel

Use the original positive smooth even $\Phi$ identified in [Romik's theta representation](../Analytic/romik2021orthogonal.md), and set

$$
d=1,\qquad V=-\log\Phi,\qquad
\psi(t)=\frac{e^{t/2}}{2\sinh t}
=\frac{e^{-t/2}}{1-e^{-2t}}.
$$

This is the density already used by the project's
[archimedean jump decomposition](../../D5/S3/Weil/ZetaGamma/ArchimedeanJumpDecomposition.lean).
Symmetry of the double integral gives the exact parameter identification

$$
D_{\psi,V}(h,h)=E_\Gamma(h):=
\int_0^\infty\psi(t)\int\Phi(x)\Phi(x+t)
|h(x+t)-h(x)|^2\,dx\,dt. \tag{2}
$$

No normalization factor is inserted into this energy. Put

$$
A=\int\Phi(x)^2\,dx,\qquad
m_2(h)=A^{-1}\int h(x)\Phi(x)^2\,dx.
$$

The function $\psi$ decreases strictly, so $\gamma(r)=\psi(r+1)$.
Near zero, $\psi(t)\sim(2t)^{-1}$; at infinity,
$\psi(t)\sim e^{-t/2}$. These estimates give both the form-integrability
condition and the inverse-kernel integral in (1), and give the positive-order
tail moment for any fixed $\alpha_0\in(0,1)$.

The [theta derivative tail bound](frankliebseiringer2006hardy.md), obtained from the original normally convergent series and evenness, gives

$$
\Phi(x)\le C e^{c|x|}\exp\bigl(-\tfrac\pi2 e^{2|x|}\bigr).
$$

It implies boundedness and integrability of $\Phi$, integrability of
$\Phi^3/\gamma$, and the stated radial-supremum limit. Positivity and
smoothness make $V$ locally bounded. Thus (1) applies and yields the unconditional paper-level source application

$$
G(h):=\int |h(x)-m_2(h)|^2\Phi(x)\gamma(|x|)\,dx
\le C_1 A E_\Gamma(h). \tag{3}
$$

In particular (3) holds for the even complex compact smooth tests of the
[theta-weighted Weil interface](lagarias2004li.md).

## The weight and constant that remain unpaid

The full even Weil interface uses

$$
d\nu(x)=2\Phi(x)\cosh(x/2)\,dx,
\qquad
E_\Gamma(h)+E_{\rm prime}(h)\ge\tfrac12\operatorname{Var}_\nu(h).
$$

Its center is $\nu(h)$, whereas (3) uses $m_2(h)$. More fundamentally, the ratio between the target density and the controlled density is

$$
\frac{2\Phi(x)\cosh(x/2)}{\Phi(x)\gamma(|x|)}
=\frac{2\cosh(|x|/2)}{\psi(|x|+1)}
\sim e^{|x|+1/2}. \tag{4}
$$

It is unbounded. Changing the center alone cannot give a uniform domination
of the target variance by this weighted integral. For example, even smooth
bumps supported near $\pm R$, normalized in $L^2(\nu)$, have
$\operatorname{Var}_\nu$ tending to one while $G$ tends to zero: the ratio
of controlled to target densities tends to zero on those supports, and
their $\mu_{2V}$ means tend to zero by Cauchy–Schwarz and the theta tail.
This is a weight-comparison observation, not a counterexample to (3) or to
the full energy bound; it does not estimate the energies of these bumps.

The source therefore supplies a genuine weaker-weight coercive estimate
for exactly $E_\Gamma$. It supplies neither the numerical constant nor the
common-test prime/Gamma comparison required at one-half. Replacing the
$\Phi^2$ speed measure by $\nu$ also changes the generator contract.
Neither an unchanged spectral gap nor a generator realization on
$L^2(\nu)$ follows from Example 2.3.

The source application, tail checks and weight comparison here are paper
deductions, not new Lean proofs or an originality claim. The source PDF has
42 pages and SHA-256
`82e717b0b790b169103b9cf1f9c39bd8612aaaf534723fad6199f6d6ecc64ca5`.
No theorem from a later journal version is used without its own source check.

## The Gamma-only target gap is zero

Use the original theta kernel and the pole probability measure from the
[even Weil interface](lagarias2004li.md):
$d\nu=2\Phi(x)\cosh(x/2)\,dx$, with
$I=\int\Phi(x)e^{x/2}\,dx=1/2$.
The following is a paper deduction from the published theta inputs and the
actual jump energy, rather than an additional theorem attributed to Chen–Wang.

Fix a nonzero real $u\in C_c^\infty((0,1))$, extended by zero. For $R\ge2$
put $\delta_R=e^{-2R}$ and

$$
h_R(x)=a_R\left[
 u\left(\frac{x-R}{\delta_R}\right)
+u\left(\frac{-x-R}{\delta_R}\right)\right],
\qquad \int |h_R|^2\,d\nu=1,
$$

with $a_R>0$. These are actual even compact smooth tests supported in
$A_R=[R,R+\delta_R]\cup[-R-\delta_R,-R]$.
[Romik's Lemma 2.3](../Analytic/romik2021orthogonal.md), printed p.10,
equations (2.8)–(2.9), supplies the upper tail and first-term remainder.
Its two-sided consequence is

$$
cg(r)\le\Phi(r)\le Cg(r),\qquad
g(r)=\exp\bigl(9r/2-\pi e^{2r}\bigr),\qquad r\ge1.
$$

The local-scale identity recorded there gives
$\Phi(r)\asymp\Phi(R)$ for $R-\delta_R\le r\le R+2\delta_R$.
This is comparison by constants, not a ratio tending to one. Thus

$$
a_R^{-2}\asymp_u\delta_R\Phi(R)e^{R/2},\qquad
N_R:=\int h_R^2\,dx\le C_u e^{-R/2}/\Phi(R),
$$

$$
\|h_R'\|_2^2=\delta_R^{-2}
\frac{\|u'\|_2^2}{\|u\|_2^2}N_R,
\qquad W_R:=\int\Phi h_R^2\,dx\le e^{-R/2}.
$$

Also $|\nu(h_R)|^2\le\nu(A_R)
=O(\delta_R\Phi(R)e^{R/2})$, so $\operatorname{Var}_\nu(h_R)\to1$.
All comparison constants here and below are independent of $R$; those
indexed by $u$ may depend on that fixed bump.

Let $S(r)=\sup_{|x|\ge r}\Phi(x)$ and
$J_R(t)=\int\Phi(x)\Phi(x+t)|h_R(x+t)-h_R(x)|^2\,dx$.
For $0<t<\delta_R$, the contributing pairs lie in the local comparison
region. The translation derivative bound gives
$J_R(t)\le C\Phi(R)^2t^2\|h_R'\|_2^2$. Since $\psi(t)\le C/t$ for $t<1$,

$$
\int_0^{\delta_R}\psi(t)J_R(t)\,dt
\le C_u\Phi(R)e^{-R/2}.
$$

This pays the derivative cost of the shrinking bump. For
$\delta_R\le t<1$, the bound $|a-b|^2\le2(|a|^2+|b|^2)$ gives
$J_R(t)\le4S(R-1)W_R$, hence

$$
\int_{\delta_R}^1\psi(t)J_R(t)\,dt
\le C_u(1+R)S(R-1)e^{-R/2}.
$$

For $t\ge1$, use $\psi(t)\le Ce^{-t/2}$ and

$$
\int\Phi(y)e^{-|x-y|/2}\,dy\le I e^{-|x|/2}.
$$

For $x\ge0$ this follows from
$e^{-|x-y|/2}\le e^{-x/2}e^{y/2}$; evenness supplies $x<0$.
It gives $\int_1^\infty\psi(t)J_R(t)\,dt\le Ce^{-R}$.
Together,

$$
E_\Gamma(h_R)\le C_u\left[
e^{-R}+(1+R)S(R-1)e^{-R/2}+\Phi(R)e^{-R/2}\right]
=O_u(e^{-R}). \tag{5}
$$

The theta tail makes the last two terms $o(e^{-R})$. Nonnegativity and
the normalized variance give the paper-level conclusion

$$
\inf_{\substack{h\in C_c^\infty(\mathbb R;\mathbb C)\ \mathrm{even}\\
                \operatorname{Var}_\nu(h)>0}}
\frac{E_\Gamma(h)}{\operatorname{Var}_\nu(h)}=0. \tag{6}
$$

Thus Gamma alone cannot control the target variance by any positive
uniform constant on this compact test class. This strengthens the
weight-comparison observation to an estimate on the actual energy and
does not conflict with (3), whose variance density is weaker.

## Exact leading Gamma compensation on the same tests

Put $f_R=\Phi h_R$ and
$\operatorname{Corr}_f(t)=\int f(x+t)\overline{f(x)}\,dx$.
For the shifts at least one, expanding the square gives the exact identity

$$
E_{\Gamma,\ge1}(h_R)
=\int |h_R(x)|^2D_{\Gamma,\rm far}(x)\,d\nu(x)
-2\Re\int_1^\infty\psi(t)\operatorname{Corr}_{f_R}(t)\,dt,
$$

$$
D_{\Gamma,\rm far}(x)=
\frac{\int_{|x-y|\ge1}\Phi(y)\psi(|x-y|)\,dy}
     {2\cosh(x/2)}.
$$

For each fixed $y$, as $x\to+\infty$,

$$
\frac{e^x}{2\cosh(x/2)}
\mathbf1_{\{|x-y|\ge1\}}\psi(|x-y|)\longrightarrow e^{y/2}.
$$

The integrand without $\Phi(y)$ is bounded by $Ce^{y/2}$, using
$\psi(s)\le Ce^{-s/2}$ for $s\ge1$ and $|x-y|\ge x-y$.
Dominated convergence and evenness therefore give
$e^{|x|}D_{\Gamma,\rm far}(x)\to I$ at both tails.
On the support of $h_R$, $|x|\in[R,R+\delta_R]$, so normalization makes
the diagonal contribution $I e^{-R}+o(e^{-R})$.

The far correlation is supported in $[2R,2R+2\delta_R]$. Writing
$M_R=\|f_R\|_2^2=O(\Phi(R)e^{-R/2})$, Cauchy–Schwarz gives

$$
\left|\int_1^\infty\psi(t)\operatorname{Corr}_{f_R}(t)\,dt\right|
\le C\delta_R e^{-R}M_R=o(e^{-R}).
$$

The two smaller-shift estimates in (5) are $o(e^{-R})$. Consequently

$$
E_\Gamma(h_R)=\tfrac12e^{-R}+o(e^{-R}). \tag{7}
$$

## Compact full-form estimate without a prime number theorem

Reuse the existing [compact full-energy identity](../../D5/S3/Weil/ZetaBridge/PrimeArchimedeanEnergyIdentity.lean)
and [prime jump decomposition](../../D5/S3/Weil/ZetaBridge/PrimeJumpDecomposition.lean).
For an even compact smooth $f$ the entire finite prime diagonal mass cancels,
leaving

$$
Q(f)=P(f)+G(f)+c_\Gamma\|f\|_2^2
-2\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}
\Re\operatorname{Corr}_f(\log n), \tag{8}
$$

where

$$
G(f)=\int_0^\infty\psi(t)\|f(\cdot+t)-f\|_2^2\,dt,
\qquad P(f)=2\left|\int e^{x/2}f(x)\,dx\right|^2,
$$

and $c_\Gamma=\Re\operatorname{digamma}(1/4)-\log\pi$.
Equation (8) is a reuse of the compact formula, not a new criterion.
For support in $A_R$, a prime correlation is possible only when
$\log n\in[2R,2R+2\delta_R]$: the same-interval differences are at most
$\delta_R<\log2$. The corresponding integer interval has length at most

$$
e^{2R}(e^{2\delta_R}-1)\le2e^2.
$$

There are therefore uniformly boundedly many possible integer terms.
Since $\Lambda(n)\le\log n$, their complete coefficient sum is
$O((R+1)e^{-R})$. Every prime power is included; no short-interval prime
number theorem is needed.

The [differentiated theta series estimate](../Analytic/romik2021orthogonal.md)
$|\Phi'(r)/\Phi(r)|\le Ce^{2r}$, together with local comparison and bump
derivative scaling, gives
$\|f_R'\|_2^2\le C_u\delta_R^{-2}M_R$.
Splitting $G$ at $\delta_R$, the translation derivative bound on the first
range and $\|f(\cdot+t)-f\|_2^2\le4\|f\|_2^2$ on the second give

$$
G(f_R)\le C_u(1+R)M_R,
\qquad P(f_R)\le C\delta_R e^R M_R.
$$

Cauchy–Schwarz bounds each correlation by $M_R$. Thus

$$
|Q(f_R)|\le C_u(1+R)M_R=o(e^{-R}). \tag{9}
$$

Also $|\nu(h_R)|^2\le\nu(A_R)=o(e^{-R})$, so
$\operatorname{Var}_\nu(h_R)=1+o(e^{-R})$.
Apply the full weighted identity from the even Weil interface to these
same tests, retaining all weighted prime diagonals:

$$
E_{\rm prime}(h_R)
=\tfrac12\operatorname{Var}_\nu(h_R)+Q(f_R)-E_\Gamma(h_R)
=\tfrac12-\tfrac12e^{-R}+o(e^{-R}). \tag{10}
$$

## Positivity on the restricted disconnected support class

For every even complex compact smooth $f$ supported in $A_R$,
$\operatorname{Corr}_f(t)=0$ for $\delta_R<t<1$. Hence
$\|f(\cdot+t)-f\|_2^2=2\|f\|_2^2$ on that range. From (8),
$P(f)\ge0$ and the complete prime coefficient bound give

$$
Q(f)\ge\left[c_\Gamma+2\int_{\delta_R}^1\psi(t)\,dt
-C(R+1)e^{-R}\right]\|f\|_2^2. \tag{11}
$$

Since $\psi(t)=(2t)^{-1}+O(1)$ near zero, the bracket is
$2R+O(1)$. It is positive for all sufficiently large $R$, uniformly over
this support class. In particular $Q(f_R)>0$ there. Equations (7), (9)
and (10) describe how the same normalized tests approach the target
energy ratio one-half from a positive full-form side.

This class does not exhaust all even compact tests. The global
same-test joint lower bound remains unproved, as do RH and Robin's full
inequality. These deductions establish no operator realization,
essential-spectrum statement or continuous transport of FIB operations.
They are independently checked paper derivations, without new Lean
certification or an originality claim; the published inputs and existing
compact identities retain their own provenance.
