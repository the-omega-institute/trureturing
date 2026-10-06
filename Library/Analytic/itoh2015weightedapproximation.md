---
bibkey: itoh2015weightedapproximation
authors: Kentaro Itoh, Ryozi Sakai, and Noriaki Suzuki
year: 2015
title: The de la Vallée Poussin Mean and Polynomial Approximation for Exponential Weight
doi: 10.1155/2015/706930
url: https://arxiv.org/abs/1311.3337v2
claim: The published weighted Favard inequality, combined with the classical Brascamp–Lieb inequality and the existing complete-prime form comparison, supplies a conditional polynomial approximation of the whole original fixed-gap spectral subspace. It supplies no matrix sign or RH conclusion.
strata_touched: []
license: bibliographic-reference-only
triage: anchor
---

# Weighted polynomial approximation in the original theta form

## Reused source statements

[Itoh–Sakai–Suzuki, arXiv:1311.3337v2](https://arxiv.org/html/1311.3337v2),
Proposition 6.2, gives, for $W=e^{-Q}\in\mathcal F(C^{2}+)$,
$1\le p\le\infty$, and absolutely continuous $g$ with $g'W\in L^p$,

$$
E_{p,n}(W,g):=\inf_{\deg r\le n}\|(g-r)W\|_p
\le C_J\frac{a_n}{n}\|g'W\|_p. \tag{WA1}
$$

Here $a_n$ is the Mhaskar–Rakhmanov–Saff number defined in its
introduction. The source attributes this Favard inequality to
Sakai–Suzuki, *On the Favard-type inequalities for exponential weights*,
Theorem 1, and their earlier Theorem 6.1. It is reused, not reproved.
The published constant $C_J=C(W,p)$ is not numerically evaluated here.
For complex $g$, apply the real estimate to its real and imaginary
parts; in $L^2$ this keeps the same constant.

[Lubinsky, arXiv:math/0701099v1](https://arxiv.org/pdf/math/0701099v1),
Definition 3.11 and Theorem 3.12, pp. 17–19, place this problem in
classical Erdős-weight approximation. Definition 7.5 and Theorem 7.6,
pp. 46–47, give the relevant weight hypotheses and warn of the extra
$\sqrt{T(a_n)}$ factor in a polynomial derivative bound. A value-only
Jackson bound is not substituted for a simultaneous derivative bound.

The classical Brascamp–Lieb variance inequality is stated as (1.3) in
[Carlen–Cordero-Erausquin–Lieb, arXiv:1106.0709v2](https://arxiv.org/html/1106.0709v2),
and attributed there to Brascamp–Lieb, DOI
[10.1016/0022-1236(76)90004-5](https://doi.org/10.1016/0022-1236(76)90004-5).
For the probability density proportional to $e^{-2Q}$ with
$Q''\ge\kappa>0$, it gives

$$
\|(f-\mu_W(f))W\|_2^2
\le\frac1{2\kappa}\|f'W\|_2^2,
\qquad \mu_W(f)=\frac{\int fW^2}{\int W^2}. \tag{WA2}
$$

Real and imaginary parts give the same assertion for complex $f$.
These are ordinary approximation and log-concavity results, not
RH-strength inequalities for the original jump form.

## Same-form comparison and an admissible auxiliary weight

Use the unchanged normalized measure $d\nu=\rho\,dx$,
$\rho=2\Phi\cosh(x/2)$, and minimal even form norm
$\|h\|_{\mathcal F}^2=\|h\|_\nu^2+D(h)$ from
[the complete weighted Fourier construction](../Weil/fukushima2011dirichlet.md#weighted-fourier-cutoff-and-a-complete-finite-cosine-family).
Its (WF2) already retains every prime power. Put

$$
\gamma_j=C_j/18,\qquad L_\rho=\gamma_1/2+1/4,
\qquad H_\rho=(\gamma_2+\gamma_1^2)/2+1/8,
\qquad K=c_0+2c_1L_\rho^2.
$$

The [original coefficient bounds (WC1)](romik2021orthogonal.md#weighted-fourier-coefficient-suppliers)
give, for $a=(\log\sqrt\rho)'$,

$$
|a(x)|\le L_\rho e^{4|x|},\qquad
|a'(x)|\le H_\rho e^{8|x|}.
$$

Indeed the second logarithmic derivative uses the $\gamma_2e^{6|x|}$
and $\gamma_1^2e^{8|x|}$ terms, and the $\log(2\cosh(x/2))$
second derivative is at most $1/4$.
For an even smooth error $e$ with the displayed finite weighted norms,
(WF2), applied to $v=\sqrt\rho\,e$, gives

$$
\|e\|_{\mathcal F}^2
\le K\|e^{4|x|}\sqrt\rho\,e\|_2^2
 +2c_1\|\sqrt\rho\,e'\|_2^2. \tag{WA3}
$$

Finiteness puts $v$ in $H^1$, so (WF2) also puts $e$ in the actual
minimal domain. No identification with a maximal energy domain is used.

To check the approximation theorem's hypotheses on an explicit weight,
write $r=|x|$, $b=13/2-\pi>0$, and set

$$
Q(x)=\frac\pi2(e^{2r}-1-2r)-b\log\cosh r,
\qquad W(x)=e^{-Q(x)},\qquad \kappa=3\pi-13/2>0. \tag{WA4}
$$

This $Q$ is even and $C^2$, with $Q(0)=Q'(0)=0$. For $r>0$,

$$
Q''(r)=2\pi e^{2r}-b\operatorname{sech}^2r\ge\kappa,
\qquad
Q'''(r)=4\pi e^{2r}+2b\operatorname{sech}^2r\tanh r>0.
$$

Thus $Q$ is nonnegative and strictly convex. Increasing $Q''$ gives
$rQ'(r)\ge2Q(r)$. The function $T(r)=rQ'(r)/Q(r)$ has limit 2 at
zero and is asymptotic to $2r$ at infinity; these limits and continuity
make it quasi-increasing. The positive continuous ratio
$Q Q''/(Q')^2$ tends to $1/2$ at zero and 1 at infinity, and is bounded
above and below away from zero. These facts verify each condition of
$\mathcal F(C^{2}+)$ in §2 of the Itoh–Sakai–Suzuki source.
No $C^3$ or $C^4$ weight-class theorem is applied.

Every original theta-series summand is positive on $r\ge0$. Retaining
its first summand, and using (WC1) for the upper bound, gives

$$
(4\pi^2-6\pi)e^{5r-\pi e^{2r}}
\le\rho(r)\le2C_0e^{5r-\pi e^{2r}}.
$$

Since $r-\log2\le\log\cosh r\le r$, put

$$
S=\sqrt{2C_0}\,2^b e^{-\pi/2},\qquad
A_W=\frac{e^{\pi/2}}{\sqrt{4\pi^2-6\pi}}.
$$

Then, on the whole real line,

$$
e^{4r}\sqrt\rho\le SW,\qquad
W/\sqrt\rho\le A_We^{4r}. \tag{WA5}
$$

The auxiliary weight changes only the approximation estimate. The
original measure, covariance, jump form, prime powers and spectral
projection remain unchanged.

## One polynomial controls value and derivative errors

For a compact smooth even complex $f$, let $r_n$ be its derivative's
$L^2(W^2dx)$ orthogonal projection onto the polynomials of degree at
most $n$. The even weight and odd $f'$ make $r_n$ odd. Put

$$
p_n^0(x)=\int_0^x r_n(t)dt,
\qquad p_n=p_n^0+\mu_W(f-p_n^0).
$$

The map $f\mapsto p_n$ is complex linear, $p_n$ is even with degree
at most $n+1$, and $\mu_W(f-p_n)=0$. Apply (WA1) to $g=f'$ and
(WA2) to this same error. Both norms are finite, since $f$ is compact
smooth and $p_n$ has polynomial growth. With

$$
C_{\mathcal F}=S\sqrt{K/(2\kappa)+2c_1},
$$

(WA3)–(WA5) give

$$
\|f-p_n\|_{\mathcal F}
\le C_{\mathcal F}C_J\frac{a_n}{n}\|f''W\|_2. \tag{WA6}
$$

All polynomials here belong to the same minimal even domain by the
[existing polynomial cutoff argument](../Weil/fukushima2011dirichlet.md#even-polynomials-in-the-same-minimal-form-norm).
The projection and the primitive are a parameter adaptation of the
published approximation and variance bounds. They are not a new
generic density, derivative or prime-distribution theorem.

## Apply to the whole existing low-spectral family

Keep the original $P_\varepsilon$ and Fourier cutoff $p_N$ of
(WF8)/(FF2). Choose the spatial cutoff from one fixed translated smooth
profile, with the same support and first-derivative properties as
(FF1)–(FF2), and $\|\chi_R''\|_\infty\le C_\chi$ independent of $R$.
Such a profile can be obtained by smoothing a unit-height transition
density of integral one inside $(0,2)$; its cumulative integral has
slope at most one. Only this second-derivative bound is additional to
the previously used cutoff properties.

For an input $h\in\operatorname{ran}P_\varepsilon$ set

$$
v=p_NUh,\quad U h=\sqrt\rho\,h,\qquad
f=\chi_Rv/\sqrt\rho,\qquad t=R+2.
$$

The Fourier multiplier is bounded by one and supported on
$[-2N,2N]$. Plancherel gives $\|v^{(j)}\|_2\le(2N)^j\|h\|_\nu$
for $j=0,1,2$. Differentiating the physical $f$, rather than treating
$Uh$ as physical-bandlimited, gives exactly

$$
f''=\rho^{-1/2}\bigl[\chi_Rv''
 +2(\chi_R'-a\chi_R)v'
 +(\chi_R''-2a\chi_R'+(a^2-a')\chi_R)v\bigr].
$$

Consequently (WA5) yields

$$
\begin{aligned}
\|f''W\|_2&\le B_{R,N}\|h\|_\nu,\\
B_{R,N}&=A_We^{4t}\bigl[4N^2+4N(1+L_\rho e^{4t})
 +C_\chi+2L_\rho e^{4t}
 +(L_\rho^2+H_\rho)e^{8t}\bigr]. \tag{WA7}
\end{aligned}
$$

This bound cancels the inverse density against the comparison weight.
It does not require a uniform unweighted bound for derivatives of
$\chi_R/\sqrt\rho$.

Let $\mathcal P_{R,N,n}h=p_n(f)$. This is one bounded complex linear
map into the even polynomials of degree at most $n+1$, and controls
**every** unit input in the same spectral subspace. The spatial and
Fourier errors of (FF1)–(FF2)/(WF8) are already at most
$\sqrt7\tau/8$ and $\tau/3$, respectively, for the choices (FF7).
Combining them with (WA6)–(WA7) gives

$$
\|(I-\mathcal P_{R,N,n})P_\varepsilon\|_{\nu\to\mathcal F}
\le\sqrt7\tau/8+\tau/3
 +C_{\mathcal F}C_JB_{R,N}a_n/n. \tag{WA8}
$$

It therefore suffices to choose $n\ge1$ with
$C_{\mathcal F}C_JB_{R,N}a_n/n\le\tau/3$.
This is an approximation of the whole spectral family, not a list of
individual polynomial tests.

For an elementary degree estimate, the source's defining MRS integral
and $Q'(r)\ge(\pi/2)e^{2r}$ for $r\ge1$ give, when $a_n\ge2$,

$$
n=\frac2\pi\int_0^1\frac{a_nuQ'(a_nu)}{\sqrt{1-u^2}}du
\ge\frac{a_n}{8}e^{a_n}.
$$

Only $1/2\le u\le3/4$ is used for the last bound. Thus
$a_n\le\log(8n)$ for every $n\ge1$, including $a_n<2$.
If $d=\max\{1,3C_{\mathcal F}C_JB_{R,N}/\tau\}$, the explicit choice

$$
n=\lceil4d\log(8d)\rceil \tag{WA9}
$$

has $n\ge d\log(8n)$ and pays the third term. For example,
$4d\log(8d)\le n\le5d\log(8d)$ and
$\log(40d\log(8d))\le4\log(8d)$ verify this inequality.
The rank is at most $\lfloor(n+1)/2\rfloor+1$.

For fixed $\varepsilon$, (FF7) has
$N=O_\varepsilon(\tau^{-1}\log(e/\tau))$ and
$e^{4R}=O_\varepsilon(\log(e/\tau)^2)$. Hence
$B_{R,N}=O_\varepsilon(\tau^{-2}\log(e/\tau)^4)$, and (WA9) gives

$$
\operatorname{rank}\mathcal P_{R,N,n}
=O_\varepsilon\bigl(\tau^{-3}\log(e/\tau)^5\bigr). \tag{WA10}
$$

This asymptotic accuracy cost is smaller than the previously prescribed
(FF8) cosine count. It does not give an evaluated practical rank:
$C_J$ and the resulting constants are not numerically certified here.
No conditioning bound or executable matrix certificate is supplied.

## Remaining sign obligation

This is a conditional paper application of the unchanged theta model
and the cited external analytic inequalities; it has not been Lean
compiled and makes no research-priority claim. It reuses (WF2), the
minimal-domain polynomial cutoff and the complete low-spectral Fourier
map instead of rebuilding their prime or domain estimates.

With $\tau=\varepsilon/8$, (WA8) provides the approximation input to
[the existing complete-window transfer](../Weil/jarohsweth2020local.md).
The retained matrix must still use the **original** full covariance and
full jump form, with target $1/2-\varepsilon/2$. The auxiliary $W^2$
mean only selects the polynomial's constant; it replaces neither the
original $\nu$ variance nor the target form. Positivity of those
matrices and cofinal $\varepsilon\downarrow0$ certificates remain
unproved. No all-degree PSD, RH, Robin, or FIB arithmetic advantage
follows from this approximation bound.
