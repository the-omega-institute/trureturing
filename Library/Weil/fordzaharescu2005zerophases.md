---
bibkey: fordzaharescu2005zerophases
authors: Kevin Ford and Alexandru Zaharescu
year: 2005
title: On the distribution of imaginary parts of zeros of the Riemann zeta function
doi: 10.1515/crll.2005.2005.579.145
url: https://arxiv.org/abs/math/0405459v2
claim: The unconditional fixed smooth-test expansion identifies prime-power event amplitudes and zero golden-unit bias in ordinate phases; it supplies no uniform signed prime-state estimate for Robin.
strata_touched: []
license: citation-only
triage: anchor
---

# Fixed zero phases, prime resonance and the golden scale

The primary source is Ford–Zaharescu,
[arXiv:math/0405459v2](https://arxiv.org/abs/math/0405459v2), updated
30 September 2004, published in *J. reine angew. Math.* **579** (2005),
145–158, [DOI 10.1515/crll.2005.2005.579.145](https://doi.org/10.1515/crll.2005.2005.579.145).
The inspected arXiv TeX archive has SHA-256
`caff1afd7d9e59ed684a134ef3ce9d2d186b2dc798bb932817284ef3ebbd0db2`.
The relevant locators are §1's correction measure and density, Theorem 1,
Corollary 2, and the range preceding equation (3.8).

The sequel cited by [Polak](../Analytic/polak2026finiterobinca.md) is
Ford–Soundararajan–Zaharescu,
[arXiv:0805.2745v3](https://arxiv.org/abs/0805.2745v3), updated
10 January 2009, *Math. Ann.* **343** (2009), 487–505,
[DOI 10.1007/s00208-008-0280-x](https://doi.org/10.1007/s00208-008-0280-x).
Its inspected TeX archive has SHA-256
`3e22ea198c27abc0ac6734c57fe0b18916209fb93d76e658eaf49bfb0671fbeb`.
The inspected scope is §1, Theorems 1–4 and Conjectures 1–5.
The applications below reuse the published results and verify their
parameter interfaces; they are not new zero-distribution theorems,
whole-paper proof audits or Lean-certified results.

## Unconditional result with fixed parameters

Let $\mathbb T=\mathbb R/\mathbb Z$. Write each actual nontrivial zero as
$\rho=\beta_\rho+i\gamma_\rho$, counting zeros with multiplicity, and
let $N(T)$ count those with $0<\gamma_\rho\le T$.
For **fixed** $\eta>0$ and **fixed** $f\in C^2(\mathbb T)$,
the original Corollary 2 gives, unconditionally,

$$
\sum_{0<\gamma_\rho\le T}f(\eta\gamma_\rho)
=N(T)\int_{\mathbb T}f(u)\,du
 +T\int_{\mathbb T}f(u)g_\eta(u)\,du+o(T).
$$

Here $\eta$ is the source's $\alpha$, not the FIB atom $\alpha$.
Its correction density vanishes unless

$$
\eta=\frac ab\frac{\log p}{2\pi},
\qquad p\text{ prime},\quad a,b\in\mathbb Z_{>0},\quad (a,b)=1.
$$

In that case,

$$
g_\eta(u)=-\frac{\log p}{\pi}
\operatorname{Re}\sum_{k\ge1}
\frac{e^{-2\pi i bku}}{p^{ak/2}}.
$$

The measure being expanded is
$T^{-1}\sum_{0<\gamma_\rho\le T}\delta_{\{\eta\gamma_\rho\}}
 -N(T)T^{-1}du$. Thus $\int g_\eta=0$:
$g_\eta$ is a signed lower-order correction, not a probability density.

## The same event amplitude in a phase observation

For any **fixed integer** $q>1$, substitute
$\eta_q=\log q/(2\pi)$ and $f(u)=e^{2\pi iu}$.
The mean of $f$ is zero. Unique prime factorization says that an integer
resonance $q^b=p^a$ with $(a,b)=1$ has $b=1$, hence $q=p^a$.
The displayed density's first Fourier coefficient therefore gives

$$
\lim_{T\to\infty}\frac1T
\sum_{0<\gamma_\rho\le T}q^{i\gamma_\rho}
=-\frac{\Lambda(q)}{2\pi\sqrt q}.
$$

At a prime-power event this is exactly $-J_q/(2\pi)$, with
$J_q=\Lambda(q)/\sqrt q$ from Polak's existing event dynamics.
At other integers it is zero. This is a direct application of the
published smooth-test theorem and its explicit density. It complements
the [existing Landau source](gonek1985landau.md), whose sum retains
$q^\rho$; replacing it by an ordinate-only sum at fixed $q$ does not
require RH here. No new event law or estimate is proved.

The first FIB window's quantity readouts are $0,2,3,7,5$ for
`[null,2,3,2 5,5]`. Each positive readout in this window is an integer
prime resonance. In particular `[2 5]` has quantity $7$, rather than a
product or a free pair of arithmetic prime factors.
The null readout $0$ has no logarithm, and the unit readout $1$ gives
$\eta=0$; both lie outside the cited $\eta>0$ theorem.
This correspondence concerns quantity readouts, not a multiplicative
structure on arbitrary FIB addresses.

## Golden eigen-scale and absence of the correction

For $\varphi=(1+\sqrt5)/2$, set
$\eta_\varphi=\log\varphi/(2\pi)$.
A prime resonance would force $\varphi^b=p^a$ with $a,b>0$.
Taking the norm in $\mathbb Q(\sqrt5)$ would give
$(-1)^b=p^{2a}$, which is impossible.
Thus the same published formula has $g_{\eta_\varphi}=0$ and reads,
for each fixed smooth test,

$$
\sum_{0<\gamma_\rho\le T}f(\eta_\varphi\gamma_\rho)
=N(T)\int_{\mathbb T}f(u)\,du+o(T).
$$

The norm test also excludes resonance for the fixed three-position
window scale $\varphi^3$. These are parameter applications of an
existing theorem, not novel FIB equidistribution results.
They distinguish the golden multiplicative eigen-scale from integer
quantity cutoffs. They do not identify these zero phases with the
quarter-turn operator $C=MJ$ on composition coordinates, or identify
$\beta_\rho$ with the FIB atom $\beta=\rho(\alpha)$.

## What the cited sequel leaves unpaid

The fixed smooth-test expansion supplies no uniform error when $q$
grows with $T$, the test becomes finer, or all events must be covered
by one bound. Four sharp phase buckets use interval indicators and
are outside the $C^2$ hypothesis. Leading equidistribution is known;
the stronger second-order interval and discrepancy formulas are
Conjectures 1–2 in the inspected sequel, which its authors explicitly
do not establish even assuming RH.

The sequel's Theorem 1(i) is an unconditional lower bound for unsigned
discrepancy. Its Theorem 1(ii) assumes RH. Theorems 2–4 also assume RH
and connect additional exponential-sum, short-prime-interval and
pair-correlation conjectures; they are not unconditional suppliers of
the needed signed upper or lower estimate.

Even the original ordinate-to-complex-zero replacement has a range:
the derivation of (3.8) uses
$\delta=50\log\log T/\log T$ and $0<\delta\log x<1$ before obtaining

$$
\sum_{0<\gamma_\rho\le T}
\bigl(x^{i\gamma_\rho}-x^{\rho-1/2}\bigr)
\ll\frac{T\log^2x}{\log T}.
$$

Fixed $x>1$ satisfies that premise eventually. The estimate cannot be
quoted at arbitrary growing $x$; the sequel's stated application
$\log x=o(\sqrt{\log T})$ is within this range.

Finally Polak's actual buffer retains the factors
$e^{(\beta_\rho-1/2)t}/[\rho(1-\rho)]$ together with the ordinate phases.
The fixed-parameter unweighted averages above do not supply this
$\beta_\rho$-dependent sum or its signed state-prime cross term
$4\epsilon_r(\log q)J_q\widehat B'(\log q^-)$.
Equality of event amplitudes does not bound that joint quantity.
No universal cone-kick inequality or lower bound for the selected
source's $I_\psi(A)$ is obtained. The strict Robin condition
$I_\psi(A)>-D^*(A)$ remains unproved.
