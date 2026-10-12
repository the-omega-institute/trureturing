---
bibkey: romik2021orthogonal
authors: Dan Romik
year: 2021
title: Orthogonal polynomial expansions for the Riemann xi function in the Hermite, Meixner–Pollaczek, and continuous Hahn bases
doi: null
url: https://doi.org/10.4064/aa200515-10-3
claim: Equations (1.6)–(1.11) define the original theta differential weight and its logarithmic kernel and give the Mellin and all-complex Fourier representations of the Riemann xi function.
strata_touched:
  - D5/S3/Analytic/Fourier/ThetaDifferentialKernel
  - D5/S3/Analytic/Fourier/XiThetaTransform
license: citation-only
triage: anchor
---

# The original theta kernel and xi

On page 2 of the Online First text, equations (1.6)–(1.9) use
`theta(t) = 1 + 2 sum(n>=1) exp(-pi*n^2*t)`,
`omega(t) = sum(n>=1) (2*pi^2*n^4*t^2 - 3*pi*n^2*t)*exp(-pi*n^2*t)`,
and `Phi(x) = 2*exp(x/2)*omega(exp(2*x))`.
Equation (1.9) explicitly states `Phi(-x) = Phi(x)` for every real x.
No absolute value occurs in the definition (1.8). Equation (1.6) also gives
the positive-index theta-tail identity; separating the two summable weights
in (1.7) gives the weighted-series formula used in the repository.

Page 1, equation (1.3), defines `Xi(z) = xi(1/2 + i*z)` for `z in C`.
Page 3, equations (1.10) and (1.11), states the Mellin representation of xi and
`Xi(z) = integral_R Phi(x)*exp(i*z*x) dx`, using that all-complex convention,
without an additional prefactor. These are published statements; their new
Lean proofs do not change their literature provenance. The repository derives the differential identity
`Phi = psi'' - psi/4`, where `psi(x)=exp(x/2)*(theta(exp(2*x))-1)/2`, and
identifies this original Phi with its fixed even theta kernel. These are
repository object identifications, not claims that the paper uses repository
names or the repository's absolute-value definition.

The paper also treats the physicists' Hermite, Meixner–Pollaczek and continuous
Hahn expansions. Their coefficient integrals, polynomial normalizations and
compact convergence estimates are separate obligations; the theta transform
alone does not establish those expansions or Cardon's equivalence involving
simple zeros and its specific measure and orthogonal polynomials.

## Derivative suppliers and their variable scopes

The [second-level concavity source](planatsole2026secondlevel.md)
states a finite-order inequality for $K(\sqrt T)$ in Csordas'
normalization $\Phi(x)=2K(x/2)$, so its receiving coordinate is
$T=x^2/4$. The [original-variable derivative counterexample](sra2026thetakernelcounterexample.md)
reports failure of a different all-order inequality for $K(u)$.
The signed neighboring-row comparison at every prescribed Jensen node
and the extra common-zero vanishing remain unpaid interfaces to these
source results. The kernel representation and the derivative reports retain their own source
provenance and cannot be counted as new RH estimates.

## Reusable theta tail and its local scale

Lemma 2.3, printed p.10, equations (2.8)–(2.9), directly supplies

$$
\Phi(r)=O\!\left(e^{9r/2-\pi e^{2r}}\right),
$$

$$
\Phi(r)-2(2\pi^2e^{9r/2}-3\pi e^{5r/2})e^{-\pi e^{2r}}
=O\!\left(e^{9r/2-4\pi e^{2r}}\right)
\qquad(r\to+\infty).
$$

Thus, with $g(r)=e^{9r/2-\pi e^{2r}}$, positivity and continuity on the
remaining compact interval give $cg(r)\le\Phi(r)\le Cg(r)$ for $r\ge1$.
For $\delta_R=e^{-2R}$ the identity

$$
\log\frac{g(R+s)}{g(R)}
=\frac92s-\pi e^{2R}(e^{2s}-1)
$$

gives $\Phi(R+s)\asymp\Phi(R)$ uniformly for
$-\delta_R\le s\le2\delta_R$. This is comparison by constants,
not a ratio tending to one.

A derivative estimate must use the normally convergent original series
(1.8), rather than differentiate the displayed remainder. Its differentiated
summands are bounded by $Ce^{13r/2}n^6e^{-\pi n^2e^{2r}}$ for $r\ge1$.
The uniformly summable series after removing its first exponential gives
$|\Phi'(r)|\le Ce^{2r}g(r)$, hence
$|\Phi'(r)/\Phi(r)|\le Ce^{2r}$.
These are paper-level applications of the source series and Lemma 2.3,
used by the [Gamma tail and same-test compensation estimates](../Weil/chenwang2012weighted.md).
They are not additional tail theorems attributed to Romik or new Lean proofs.

## Explicit original-series majorants

The normally convergent source series also supplies coarse constants for
the [prime-diagonal error transfer](../Weil/trudgian2014pnt.md) and the
[full mixed-operator cutoff estimates](../Weil/lenz2010compactness.md).
These are analytic upper bounds, not fitted numerical values or new
theta representation theorems.

For $x\ge0$, put $u=e^{2x}\ge1$ and $v_n=\pi n^2u$. Differentiating
the original series gives

$$
\begin{aligned}
\Phi(x)&=2u^{1/4}\sum_{n\ge1}(2v_n^2-3v_n)e^{-v_n},\\
\Phi'(x)&=u^{1/4}\sum_{n\ge1}
             (-8v_n^3+30v_n^2-15v_n)e^{-v_n}.
\end{aligned} \tag{TS}
$$

For $H=\Phi/2+|\Phi'|$, positivity of $\Phi$ and the triangle inequality
therefore give

$$
H(x)\le u^{1/4}\sum_{n\ge1}
                   (8v_n^3+32v_n^2+15v_n)e^{-v_n}. \tag{HM}
$$

Use $u^{1/4}\le u=v_n/(\pi n^2)$, $\pi>3$,
$\sum_{n\ge1}n^{-2}\le2$, and the standard maximum
$v^ke^{-v}\le k^ke^{-k}$. The elementary lower bounds
$e^4>54$, $e^3>20$ and $e^2>7$ yield

$$
\begin{aligned}
\|\Phi\|_\infty&\le\frac83\frac{27}{e^3}<\frac{18}{5},\\
H_\infty&\le\frac23\left(
             \frac{1024}{27}+\frac{216}{5}+\frac{60}{7}\right)<60.
\end{aligned} \tag{SC}
$$

Evenness extends these bounds to the whole real line. For the weighted
integral, use evenness of $H$, $\cosh(x/2)\le e^{x/2}$ for $x\ge0$,
and $u^{1/2}\le u$. Substitution $dx=du/(2u)$ gives

$$
\begin{aligned}
M_H:=\int H(x)e^{x/2}\,dx
&=2\int_0^\infty H(x)\cosh(x/2)\,dx\\
&\le\sum_{n\ge1}\frac1{\pi n^2}
           \int_0^\infty(8v^3+32v^2+15v)e^{-v}\,dv\\
&\le\frac{254}{3}<85.
\end{aligned} \tag{MC}
$$

The polynomial integral is $8\cdot6+32\cdot2+15=127$.
Its extension from $v\ge\pi n^2$ to $v\ge0$ only increases the bound.

For a spatial tail majorant, split the exponential in (TS) and use
$v^3e^{-v/2}\le216e^{-3}<216/20$. Since $v_n\ge3u$,

$$
\Phi(x)\le\frac{144}{5}\exp\left(-\frac32e^{2|x|}\right). \tag{ST}
$$

Consequently, for $r\ge0$,

$$
T(r):=\int_{|x|>r}\Phi(x)\,dx
\le\frac{96}{5}e^{-2r}\exp\left(-\frac32e^{2r}\right). \tag{IT}
$$

Indeed, the substitution $u=e^{2x}$ on each even tail gives
$(144/5)\int_{e^{2r}}^\infty e^{-3u/2}\,du/u$;
bound $1/u$ by $e^{-2r}$ and integrate the remaining exponential.
All constants are deliberately loose and keep the original kernel and
normalization. These model applications have no new Lean certification
or originality claim.

## Weighted Fourier coefficient suppliers

For the [weighted Fourier cutoff](../Weil/fukushima2011dirichlet.md), define
on the whole real line

$$
s(x)=\sqrt{\frac{\Phi(x)}{2\cosh(x/2)}}.
$$

The existing strictly positive smooth even original kernel makes $s$
smooth and even, including at zero. The following original-series
estimates supply $s\in H^3(\mathbb R)$, bounded $s,s'$, and the derivative
summability of the complete prime graph. They are model deductions from
the source series, with no useful numerical constant sizes or new Lean
certification asserted.

For $x\ge0$, $u=e^{2x}\ge1$, write

$$
\Phi(x)=\sum_{n\ge1}
 (4\pi^2n^4e^{9x/2}-6\pi n^2e^{5x/2})e^{-\pi n^2u}.
$$

Every summand is positive. Its first summand gives
$\Phi(x)>18e^{5x/2}e^{-\pi u}$, using $\pi>3$.
Define derivative polynomials by

$$
P_{0,a}(z)=1,\qquad
P_{j+1,a}(z)=(a-2z)P_{j,a}(z)+2zP'_{j,a}(z),\qquad
P_{j,a}(z)=\sum_{k=0}^jp_{j,a,k}z^k.
$$

Direct differentiation gives
$\partial_x^j(e^{ax}e^{-\pi n^2u})
=e^{ax}e^{-\pi n^2u}P_{j,a}(\pi n^2u)$.
For $0\le j\le3$ let

$$
C_j=\sum_{n\ge1}e^{-\pi(n^2-1)}
\left(4\pi^2n^4\sum_{k=0}^j|p_{j,9/2,k}|\pi^kn^{2k}
 +6\pi n^2\sum_{k=0}^j|p_{j,5/2,k}|\pi^kn^{2k}\right).
$$

Normal convergence of the original series permits termwise
differentiation. Using $u^k\le u^j$ and
$e^{-\pi(n^2-1)u}\le e^{-\pi(n^2-1)}$ gives

$$
|\Phi^{(j)}(x)|\le C_je^{(9/2+2j)x}e^{-\pi u},\qquad
\frac{|\Phi^{(j)}(x)|}{\Phi(x)}
\le\gamma_je^{(2+2j)x},\quad\gamma_j=C_j/18. \tag{WC1}
$$

These constants have explicit tail majorants. For $q\le10$, $n\ge2$,
the ratio of successive terms $a_n=n^qe^{-\pi(n^2-1)}$ is at most
$r_*=(3/2)^{10}e^{-5\pi}<1$. Every monomial in $C_j$ has degree at
most ten, so its tail after $N\ge1$ is at most
$a_{N+1}/(1-r_*)$, with its displayed coefficient retained.

Put $d=2\cosh(x/2)$ and $\ell=\log s$. The first three derivatives of
$\log d$ have absolute bounds $1/2,1/4,1/4$. Thus

$$
|\ell'|\le A_1e^{4x},\quad |\ell''|\le A_2e^{8x},\quad
|\ell'''|\le A_3e^{12x},
$$

where

$$
\begin{aligned}
A_1&=\gamma_1/2+1/4,\\
A_2&=(\gamma_2+\gamma_1^2)/2+1/8,\\
A_3&=(\gamma_3+3\gamma_1\gamma_2+2\gamma_1^3)/2+1/8.
\end{aligned}
$$

Since $d\ge e^{x/2}$, (WC1) gives
$s\le\sqrt{C_0}\,u e^{-\pi u/2}$. Apply
$s'=s\ell'$, $s''=s((\ell')^2+\ell'')$, and
$s'''=s((\ell')^3+3\ell'\ell''+\ell''')$ to obtain

$$
|s^{(j)}(x)|\le\sqrt{C_0}B_ju^{1+2j}e^{-\pi u/2},\qquad
(B_0,B_1,B_2,B_3)=(1,A_1,A_1^2+A_2,A_1^3+3A_1A_2+A_3).
$$

For $c=3/8$, $\zeta=\pi/2-c>0$, define
$v_m=\max\{1,m/\zeta\}$, $M_m=v_m^me^{-\zeta v_m}$ and
$K_j=\sqrt{C_0}B_jM_{1+2j}$. Maximizing the remaining scalar factor,
and then using evenness, yields

$$
|s^{(j)}(x)|\le K_je^{-c e^{2|x|}}
\qquad(x\in\mathbb R,\ 0\le j\le3). \tag{WC2}
$$

Substitution on the two tails gives, with the unitary Fourier convention,

$$
\begin{aligned}
\|s^{(j)}\|_2^2&\le K_j^2\frac{e^{-2c}}{2c},\\
\|s\|_{H^3}^2
:=\int(1+\xi^2)^3|\widehat s(\xi)|^2d\xi
&\le\frac{e^{-2c}}{2c}\sum_{j=0}^3\binom3jK_j^2,\\
\|(s^2)'\|_\infty&\le2K_0K_1.
\end{aligned} \tag{WC3}
$$

For the prime operator use the same coefficients as in the mixed model:
$t_n=\log n$, $w_n=\Lambda(n)/\sqrt n$ and
$b_n(x)=w_ns(x)s(x+t_n)$. Product differentiation and
$e^{2|x|}+e^{2|x+t_n|}\ge2n$ imply
$\|b_n'\|_\infty\le2K_0K_1w_ne^{-2cn}$.
With $r=e^{-2c}$ and $w_n\le n$,

$$
\sum_{n\ge2}\|b_n'\|_\infty
\le2K_0K_1\left(\frac r{(1-r)^2}-r\right)<\infty. \tag{WC4}
$$

This sum is per representative undirected edge and includes every prime
power. The translated adjoint has the same derivative supremum norm, so
the explicitly two-direction estimate is

$$
\sum_{n\ge2}\left(\|b_n'\|_\infty+
 \|(b_n(\cdot-\log n))'\|_\infty\right)
\le4K_0K_1\left(\frac r{(1-r)^2}-r\right). \tag{WC5}
$$

These estimates discharge the coefficient hypotheses in (WF2), (WF5)
and (WF7) of the linked cutoff construction for the actual theta model.
They retain the full graph and provide deliberately coarse constants;
useful bandwidth and matrix certificates require further quantitative
work.

## Fixed theta truncation in signed Laguerre projections

The prescribed-node comparison uses the complete kernel, not its first theta
summands. Write, in the normalization $\Phi(x)=2K(x/2)$,

$$
k_m(u)=\pi m^2(2\pi m^2e^{4u}-3)e^{5u-\pi m^2e^{4u}},\qquad
K_N(u)=\sum_{m=1}^N k_m(u),\qquad K(u)=\sum_{m\ge1}k_m(u).
$$

Keep $\xi_0=\xi(1/2)>0$ and the original receiving measure

$$
d\mu(T)=\frac{4K(\sqrt T)}{\xi_0\sqrt T}\,dT,\qquad
d\mu_N(T)=\frac{4K_N(\sqrt T)}{\xi_0\sqrt T}\,dT.
$$

The latter is not renormalized. For fixed $v>0$ and fixed integer $N\ge1$,
define $J_n(v)=\int L_n^{-1/2}(T/v)\,d\mu(T)$ and $J_{n,N}(v)$ with
$\mu_N$ in place of $\mu$. The standard endpoint-coefficient calculation
below gives the actual-source application

$$
\begin{aligned}
\kappa_N:=K_N'(0)&>0,\\
J_{n,N}(v)&=-\frac{2v\kappa_N}{\xi_0\sqrt\pi}\,n^{-3/2}
                  +O_{N,v}(n^{-9/4}),\\
J_n(v)&=O_{A,v}(n^{-A})\qquad\text{for every }A>0.
\end{aligned} \tag{LC1}
$$

This is an application of classical Laguerre facts and the original source
series. It is neither a theorem attributed to Romik nor a new Lean result or
an originality claim. The reusable suppliers are the Laguerre weight and
norm in [DLMF 18.3, Table 1](https://dlmf.nist.gov/18.3), its differential
equation in [18.8, Table 1](https://dlmf.nist.gov/18.8), its finite series in
[18.5.12](https://dlmf.nist.gov/18.5.E12), the terminating
Chu–Vandermonde evaluation [15.4.24](https://dlmf.nist.gov/15.4.E24), and the
gamma-ratio asymptotic [5.11.12](https://dlmf.nist.gov/5.11.E12).
Weniger's [*On the Analyticity of Laguerre Series*, arXiv:0808.3926v1](https://arxiv.org/abs/0808.3926v1),
section 3, equations (3.2)–(3.3), printed p.9, supplies the fractional-power
integral and its weighted $L^2$ expansion directly. For $\alpha>-1$,
real $\rho\notin\mathbb N_0$ and $\alpha+2\rho>-1$, its integral formula
specialized to $\alpha=-1/2,\rho=1/2$ gives
$-\Gamma(n-1/2)/(2\sqrt\pi\,\Gamma(n+1))$.
This is the unnormalized projection; division by the Laguerre norm gives
the series coefficient $-1/(\sqrt\pi(2n-1))$. These two coefficient
normalizations must not be compared as different decay mechanisms.

First, termwise differentiation of the normally convergent theta series gives

$$
k_m'(0)=\pi m^2e^{-\pi m^2}
       \bigl[-8(\pi m^2)^2+30\pi m^2-15\bigr].
$$

For $m\ge2$ the bracket is negative. Complete-source evenness gives
$K'(0)=0$, so $\kappa_N=-\sum_{m>N}k_m'(0)>0$.

For the coefficient correspondence set $x=T/v$,
$w(x)=x^{-1/2}e^{-x}$ and $g_v(x)=e^xK(\sqrt{vx})$. Then

$$
J_n(v)=\frac{4\sqrt v}{\xi_0}\langle g_v,L_n^{-1/2}\rangle_w,\qquad
\mathcal D=-x\partial_x^2-(\tfrac12-x)\partial_x
          =-w^{-1}\partial_x(xw\partial_x),\qquad
\mathcal D L_n^{-1/2}=nL_n^{-1/2}.
$$

The full kernel is even analytic at zero. For every integer $j\ge0$, the
normally convergent differentiated source series gives a finite $B_j$ with

$$
|K^{(j)}(u)|\le B_j\exp\bigl((4j+9)u-(\pi/2)e^{4u}\bigr)
\qquad(u\ge0).
$$

Indeed, $k_m^{(j)}(u)=\pi m^2e^{5u-\pi m^2e^{4u}}
P_j(\pi m^2e^{4u})$ for a polynomial of degree $j+1$; splitting the
exponential leaves a summable polynomially weighted theta tail.
Consequently $\mathcal D^rg_v\in L^2(w)$ for each integer $r\ge0$.
At zero these iterates and their first derivatives are bounded; at infinity
they decay. The Green boundary term

$$
\left[x^{1/2}e^{-x}
 \bigl(f'L_n^{-1/2}-f(L_n^{-1/2})'\bigr)\right]_0^\infty
$$

vanishes for $f=\mathcal D^jg_v$ at every integration by parts, and for
$f=h,\mathcal Dh$ in the finite-source argument below. For $n\ge1$,

$$
|\langle g_v,L_n^{-1/2}\rangle_w|
\le n^{-r}\|\mathcal D^rg_v\|_w\|L_n^{-1/2}\|_w,
\qquad
\|L_n^{-1/2}\|_w^2=\frac{\Gamma(n+1/2)}{n!}=O(n^{-1/2}).
$$

Taking $r$ arbitrarily large yields the complete-source statement in (LC1).

For the finite sum, $g_{N,v}(x)=e^xK_N(\sqrt{vx})$ has a convergent
Puiseux expansion at zero. Subtract its $x^{1/2}$ and $x^{3/2}$ terms,
whose coefficients are $a=\sqrt v\,\kappa_N$ and some $c$, respectively.
The remaining function has the local form

$$
h(x)=a_0+a_1x+x^2A(x)+x^{5/2}B(x),
$$

with $A,B$ analytic near zero. Consequently $h'$ and $(\mathcal Dh)'$
are bounded there, and $\mathcal D^2h$ is locally in $L^2(w)$. At infinity,
$h$ and its iterates are a finite combination of half-integer powers and
rapidly decaying differentiated source terms. They belong to the required
weighted spaces, and both Green boundary terms vanish. Two integrations
by parts thus give
$\langle h,L_n^{-1/2}\rangle_w=O_{N,v}(n^{-9/4})$.
The convergent expansion, rather than differentiation of an $O(x^2)$
remainder, supplies these endpoint derivative bounds.

Integrating the standard finite Laguerre series and applying
Chu–Vandermonde gives, for real $s>-1/2$,

$$
\int_0^\infty x^{s-1/2}e^{-x}L_n^{-1/2}(x)\,dx
=\Gamma(s+1/2)\frac{(-s)_n}{n!}.
$$

The $x^{1/2}$ coefficient is therefore
$-n^{-3/2}/(2\sqrt\pi)+O(n^{-5/2})$; the $x^{3/2}$ coefficient is
$O(n^{-5/2})$. The prefactor $4\sqrt v/\xi_0$ produces (LC1).
In particular, the omitted infinite theta tail cancels the displayed
$n^{-3/2}$ leading term of the fixed finite sum.

This is a fixed-$v$, fixed-$N$ asymptotic. It is not a counterexample at
the moving full-source nodes $v=n\lambda$ with
$\operatorname{sourceQ}_n(\lambda)=0$, and it does not exclude
degree-dependent truncations. Small absolute kernel tails alone do not
give a small relative error in these signed projections. The required
all-node comparison remains
$\beta a^2-ab\ge0$, where $a=C_{n-1,0}(v)$,
$b=h_1C_{n,1}(v)$ and $\beta=n(n-1/2)v^2$. Neither (LC1) nor the
classical coefficient suppliers control its margin near $a=0$;
common-zero vanishing and multiplicity propagation also remain separate.

## Global scope of finite evenization

Finite evenization is valid for local derivative calculations with a
retained analytic tail bound, but does not furnish a globally positive
substitute for the receiving measure. For fixed $N\ge1$, put
$E_N(u)=K_N(u)+K_N(-u)$. Directly from the finite source series,

$$
\lim_{u\to+\infty}e^{5u}E_N(u)
=-3\pi\sum_{m=1}^Nm^2<0.
$$

Indeed, $e^{5u}K_N(u)\to0$, whereas each summand of
$e^{5u}K_N(-u)$ tends to $-3\pi m^2$. Thus $E_N$ is eventually
negative and has an exponential tail, while the full even source $2K$
is positive with super-exponential tails. A positive approximation usable
for the complete signed projections must address both endpoint evenness
and the full tail behavior. This application places no additional
restriction on the separate local derivative certificate linked from the
second-level source note.

## A positive smooth splice and its absolute error interface

A standard smooth cutoff repairs these two representation defects without
altering the full-source target. Choose an even $C^\infty$ function $\chi$
with $0\le\chi\le1$, equal to one for $|u|\le1/16$ and zero for
$|u|\ge1/8$. For $N\ge1$ define

$$
H_N(u)=(1-\chi(u))K_N(|u|)
       +\frac{\chi(u)}2\bigl(K_N(u)+K_N(-u)\bigr).
\tag{LC2}
$$

Near zero the first term vanishes identically and the remaining expression
is even analytic. Away from zero both terms are smooth, including the
cutoff transition, so $H_N$ is even and $C^\infty$ on the whole line.
For $|u|\le1/8$, every summand of both $K_N(u)$ and $K_N(-u)$ is positive:
$2\pi m^2e^{\pm4u}\ge2\pi e^{-1/2}>3$.
In the cutoff transition (LC2) is a convex combination of positive
expressions; outside it $H_N=K_N(|u|)>0$. Thus $H_N$ is strictly positive
and retains the super-exponential far tail and its differentiated bounds.

Set $R_N=K-K_N$. Complete-source evenness gives, for $u\ge0$,

$$
K(u)-H_N(u)
 =\bigl(1-\chi(u)/2\bigr)R_N(u)
   +\frac{\chi(u)}2R_N(-u)\ge0. \tag{LC3}
$$

Here $R_N(u)>0$ for all $u\ge0$. Nonnegativity of $R_N(-u)$ is used
only on the cutoff support $0\le u\le1/8$, where its individual
summands are positive; it is not asserted on the entire positive half-line.

Keep the same $\xi_0$ and put
$d\mu_{H_N}=4H_N(\sqrt T)/(\xi_0\sqrt T)\,dT$, without renormalization.
Let $J_{n,H_N}(v)=\int L_n^{-1/2}(T/v)\,d\mu_{H_N}(T)$ and
$G_{N,v}(x)=e^x(K-H_N)(\sqrt{vx})$. For fixed $v>0,N\ge1$,
$G_{N,v}$ is analytic at zero and has the required rapid derivative
decay at infinity. Every $\mathcal D^rG_{N,v}$ belongs to $L^2(w)$,
and all its Green boundary terms vanish. The same classical Laguerre
calculation therefore supplies, for integers $n\ge1,r\ge0$,

$$
|J_n(v)-J_{n,H_N}(v)|
\le\frac{4\sqrt v}{\xi_0}n^{-r}
 \left(\frac{\Gamma(n+1/2)}{n!}\right)^{1/2}
 \|\mathcal D^rG_{N,v}\|_w. \tag{LC4}
$$

For fixed $v,r$, the final norm tends to zero as $N\to\infty$.
On compact intervals this follows from differentiated theta-tail
convergence, with evenness handling zero; on the remaining half-line the
original-series derivative bounds provide an integrable majorant.
Thus (LC4) removes the artificial algebraic endpoint term of the bare
finite sum. It is a standard cutoff application and an absolute error
interface, not a new approximation theorem attributed to the source or a
literature novelty claim.

Pointwise nonnegative density error does not determine the sign of a
Laguerre projection. The norm in (LC4) depends on $v,r$ and the cutoff;
no uniform moving-node bound or useful numerical constant is supplied.
Passing to monic Laguerre projections also introduces their degree-dependent
normalization factors. In particular, neither (LC3) nor (LC4) compares the
correlated error with the signed margin $\beta a^2-ab$ at the original
nodes, especially near $a=0$. The original all-node inequality,
common-zero vanishing and multiplicity propagation remain unproved.
This source-specific analytic interface has not been checked in Lean.

## Explicit polynomial moments and one correlated tail projection

The same $H_N$ supplies an explicit error bound for every polynomial;
no second cutoff construction is required. Put $\delta=1/8$, $M=N+1$
and $d\nu_N=d\mu-d\mu_{H_N}$. Equation (LC3) gives, for $u\ge0$,

$$
0\le K(u)-H_N(u)
\le R_N(u)+\tfrac12\mathbf1_{[0,\delta]}(u)R_N(-u).
$$

For $c=\pi$ or $c=\pi e^{-4\delta}$ define

$$
U_M(c)=\frac{M^4e^{-cM^2}}
 {1-(1+1/M)^4e^{-c(2M+1)}}.
$$

The successive-term ratio of $m^4e^{-cm^2}$ decreases with $m$;
for $M\ge2$ and $c\ge\pi e^{-1/2}>3/2$ it is strictly less than one.
Thus $\sum_{m\ge M}m^4e^{-cm^2}\le U_M(c)$.
The original summands satisfy

$$
\begin{aligned}
0<k_m(u)&\le2\pi^2m^4e^{-\pi m^2}
             e^{-(4\pi m^2-9)u} &&(u\ge0),\\
0<k_m(-u)&\le2\pi^2m^4e^{-\pi e^{-4\delta}m^2}
                                      &&(0\le u\le\delta).
\end{aligned}
$$

The first bound uses $e^{4u}\ge1+4u$. Substitution $T=u^2$ gives
$d\nu_N=8(K-H_N)(u)\,du/\xi_0$. Integrating these envelopes against
$u^{2j}$ yields, for integers $j\ge0$,

$$
\int T^j\,d\nu_N\le\overline M_j(N)
:=\frac{16\pi^2}{\xi_0}
 \left[
 \frac{(2j)!\,U_M(\pi)}{(4\pi M^2-9)^{2j+1}}
 +\frac{\delta^{2j+1}}{2(2j+1)}U_M(\pi e^{-4\delta})
 \right]. \tag{LC5}
$$

Consequently, for $P(T)=\sum_jp_jT^j$,
$|\int P\,d\nu_N|\le\sum_j|p_j|\overline M_j(N)$.
All degree and $v$ dependence remains in the polynomial coefficients;
this finite-parameter bound also applies at the unchanged full-source nodes.

Write $\Pi_{j,v}^{(\alpha)}(T)=(-1)^jj!v^jL_j^{(\alpha)}(T/v)$,
$P_j=\Pi_{j,v}^{(-1/2)}$, and for $n\ge1$ set
$\eta=\beta/(2n)=(n-1/2)v^2/2$.
The classical contiguous and derivative identities
[DLMF 18.9.13](https://dlmf.nist.gov/18.9.E13),
[18.9.14](https://dlmf.nist.gov/18.9.E14) and
[18.9.23](https://dlmf.nist.gov/18.9.E23) give, in this normalization,

$$
\begin{aligned}
F_{n,v}(T)&:=(T+v/2)P_n(T)+\eta P_{n-1}(T)\\
 &=T\left(P_n(T)+\frac{v}{2n}P_n'(T)\right)
 =T^2\Pi_{n-1,v}^{(3/2)}(T). \tag{LC6}
\end{aligned}
$$

This is direct reuse of those identities, not a new polynomial theorem.
It cancels the constant and linear endpoint coefficients before estimating
the joint tail. At the same full-source node $\int P_n\,d\mu=0$, let

$$
a_H=\int P_{n-1}\,d\mu_{H_N},\qquad
b_H=\int TP_n\,d\mu_{H_N},\qquad
c_H=\int P_n\,d\mu_{H_N},\qquad
D_N=b_H+\eta a_H+(v/2)c_H.
$$

Then $b+\eta a=D_N+\mathcal R_N$, where
$\mathcal R_N=\int F_{n,v}\,d\nu_N$.
The approximation's $c_H$ need not vanish at the full-source node and
cannot be dropped. The finite Laguerre series supplies the coefficient
absolute values, and (LC5) gives the independently estimable bound

$$
|\mathcal R_N|\le E_F(n,v,N)
:=\sum_{j=2}^{n+1}
 \frac{(n-1)!v^{n+1-j}}{(j-2)!}
 \binom{n+1/2}{n+1-j}\overline M_j(N). \tag{LC7}
$$

Thus the independent comparison
$aD_N+|a|E_F\le(\beta+\eta)a^2$ would imply $\beta a^2-ab\ge0$,
with no restriction on the sign of $a$. This comparison has not been
established for every actual node. Positive residual measure alone is
insufficient: $F_{2,v}(T)=T^2(T-5v/2)$ changes sign.
At a collision $a=0=\int P_n\,d\mu$, the scalar inequality is automatic;
the separate required equality is $D_N+\mathcal R_N=b=0$.
Neither the explicit absolute bound nor the endpoint cancellation supplies
that equality or multiplicity propagation. These source-specific error
applications are ordinary analysis, with no Lean or originality claim;
RH and all-integer strict Robin remain unproved.

## Source anomalies retained

On page 40 the printed c-prime integral omits the factor `2*sqrt(2)` used in the
original c coefficients, while asserting equality of the even coefficients.
The Pollaczek prose says orthonormal, whereas equation (A.12) gives a nonunit
norm. Neither discrepancy is silently repaired or used as an equality here.
The separate Cardon source's odd-extension/jump and recurrence/tail issues
remain separate from Romik's theta formulas.

## Verified locator

- URL: https://doi.org/10.4064/aa200515-10-3
- DOI: 10.4064/aa200515-10-3

The author-hosted Online First PDF was retrieved on 2026-09-11 from
https://www.math.ucdavis.edu/~romik/data/uploads/papers/riemannxi-acta-online-first.pdf.
Its SHA-256 is `a28edcf341776bf801e9d0c2de4631639b2c46c579a67a38cc2788d255e2ae87`.
The page references above use that 72-page PDF's internal pagination; they are
not converted to the final Acta Arithmetica 200(3), 259–329 pagination.
