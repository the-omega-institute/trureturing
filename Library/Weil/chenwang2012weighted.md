---
bibkey: chenwang2012weighted
authors: Xin Chen and Jian Wang
year: 2012
title: Weighted Poincare Inequalities for Nonlocal Dirichlet Forms
doi: null
url: https://arxiv.org/abs/1207.7140v1
claim: Theorem 5.1 supplies a weighted Poincare estimate for the exact theta Gamma jump energy, centered in the Phi-squared measure. Its controlled weight and unspecified constant do not supply the pole-weighted variance bound at one-half required by the full Weil form.
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
