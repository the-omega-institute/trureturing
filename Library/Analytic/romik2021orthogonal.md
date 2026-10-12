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

## A parameter-adapted direction for the correlated residual

The endpoint mechanism is the classical Laplace method,
[DLMF §2.3(iii), equations 2.3.13–2.3.17](https://dlmf.nist.gov/2.3.iii).
For each forward theta summand its phase is $p(u)=e^{4u}$, its large
parameter is $\pi m^2$, and its two factored amplitudes are
$(1-\chi(u)/2)u^4q(u^2)e^{\ell u}$ for $\ell=5,9$, with $q$ below.
Here $n,v,\chi$ are fixed as $m\to\infty$; the outside scalar
coefficients are $-3\pi m^2$ for $\ell=5$ and $2\pi^2m^4$ for
$\ell=9$.
The phase has a unique endpoint minimum; the amplitude is analytic near
zero because $\chi=1$ there, and the integral converges absolutely.
In the DLMF notation, the endpoint exponents are $\mu=1$ and
$\lambda=5$, with leading phase coefficient $4$ and leading amplitude
coefficient $A/2$. This directly supplies the fixed-parameter endpoint
sign mechanism. It gives no asymptotic for the entire reflected residual;
that contribution is retained through its favorable support. The following
explicit comparison quantifies this source application without using an
uncontrolled asymptotic remainder.

The classical finite Laguerre series and the original theta-tail envelope
give a direction for (LC7) after a parameter-dependent cutoff. Fix an
integer $n\ge1$ and $v>0$, and put

$$
s=(-1)^{n-1},\qquad
q(T)=s\Pi_{n-1,v}^{(3/2)}(T),\qquad
A=q(0)=v^{n-1}(5/2)_{n-1}>0,\qquad
r_0=\sqrt{v/(4n)}.
$$

The finite-series coefficients already used in (LC7) give

$$
\left|q(T)/A-1\right|
\le \exp\!\left(\frac{2(n-1)T}{5v}\right)-1\quad(T\ge0),
\qquad
q(T)\ge A/2\quad(0\le T\le r_0^2). \tag{LC8}
$$

Indeed, the absolute value of its $k$th coefficient after division by
$A$ is $\binom{n-1}{k}/((5/2)_kv^k)$, at most
$(2(n-1)/(5v))^k/k!$. On the stated interval the exponential argument
is at most $(n-1)/(10n)<1/10$, so $2-e^{1/10}>1/2$ suffices.
For $n=1$ the polynomial is constant. This is an application of the
[classical finite series, DLMF 18.5.12](https://dlmf.nist.gov/18.5.E12),
without any hyperbolicity assumption on the source Jensen polynomials.

Take $\delta=\min(1/8,r_0/2)$ and use the same construction (LC2), now
with an even smooth $\chi$ equal to one on $|u|\le\delta/2$ and zero
on $|u|\ge\delta$. Denote the resulting splice by $H_{N,\delta}$,
and use it in $\nu_N$ and $\mathcal R_N$. Its smoothness, positivity
and unrenormalized measure follow from the preceding construction.
The reflected part of (LC3) is supported in the favorable region of
(LC8); for $u\ge r_0$ the residual is exactly $R_N(u)$.

For $M=N+1\ge2$ set $h=\min(r_0,M^{-2})$. On $0\le u\le h$,
(LC3) gives $K-H_{N,\delta}\ge k_M(u)/2$, and (LC8) gives
$sF_{n,v}(u^2)\ge Au^4/2$. The remaining exponential factors give
the following positive contribution, before the common factor $8/\xi_0$:

$$
L_M=\frac{A\pi M^2(2\pi M^2-3)}{20}
       h^5\exp\!\left(-\pi M^2e^{4h}\right). \tag{LC9}
$$

Here the factor $20$ is $2\cdot2\cdot5$: the two preceding halves
and $\int_0^h u^4\,du=h^5/5$.

To bound the possibly adverse part on $u\ge r_0$, put
$c=\pi e^{4r_0}$ and $\Lambda_M=4cM^2-9>0$. With $u=r_0+t$,
the original source summands satisfy

$$
k_m(r_0+t)\le2\pi^2e^{9r_0}m^4e^{-cm^2}
                                      e^{-(4cm^2-9)t}\quad(t\ge0).
$$

Use $U_M(c)$ from (LC5), and write $F_{n,v}(T)=\sum_{j=2}^{n+1}f_jT^j$
with the coefficient absolute values in (LC7). Expanding
$(r_0+t)^{2j}$ and integrating each exponential monomial yields

$$
B_M=2\pi^2e^{9r_0}U_M(c)
 \sum_{j=2}^{n+1}|f_j|
 \sum_{\ell=0}^{2j}\binom{2j}{\ell}
       r_0^{2j-\ell}\frac{\ell!}{\Lambda_M^{\ell+1}},
\qquad
s\mathcal R_N\ge\frac8{\xi_0}(L_M-B_M). \tag{LC10}
$$

All residual contributions on $[0,r_0]$, including the entire reflected
tail, are favorable; their portion not used in $L_M$ may be omitted from
this lower bound. No reflected-tail positivity is asserted outside the
cutoff support.

An explicit sufficient threshold follows by putting

$$
\begin{aligned}
d&=c-\pi>0,& D&=1-(3/2)^4e^{-5c}>0,\\
C_F&=\sum_{j=2}^{n+1}|f_j|
       \sum_{\ell=0}^{2j}\binom{2j}{\ell}r_0^{2j-\ell}\ell!,&
C&=\frac{40e^{9r_0+4\pi(e-1)}C_F}{cDA}.
\end{aligned}
$$

If $M^2\ge\max(4,1/r_0)$, then $h=M^{-2}$ and
$M^2(e^{4/M^2}-1)\le4(e-1)$. Also
$\Lambda_M\ge cM^2\ge1$ and the denominator of $U_M(c)$ is at least
$D$. Consequently

$$
L_M\ge\frac{A\pi^2}{20}M^{-6}
               e^{-\pi M^2-4\pi(e-1)},\qquad
\frac{B_M}{L_M}\le CM^8e^{-dM^2}. \tag{LC11}
$$

The last expression is nonincreasing once $M^2\ge4/d$ and tends to
zero. Thus a single integer $M\ge2$ satisfying

$$
M^2\ge\max(4,1/r_0,4/d),\qquad CM^8e^{-dM^2}<1 \tag{LC12}
$$

certifies $s\mathcal R_N>0$ for $N=M-1$ and every larger cutoff,
with the same $n,v,\delta$. Such a threshold exists for every fixed
$n,v$. All constants depend on those parameters; this supplies no single
cutoff uniform over the moving full-source nodes.

At an unchanged actual node, compute $a_H,b_H,c_H,D_N$ using this
$H_{N,\delta}$ and retain the $(v/2)c_H$ term, which need not vanish, as in (LC6)–(LC7).
If $sa\le0$, (LC12) makes $-a\mathcal R_N\ge0$, so the separate
comparison

$$
aD_N\le(\beta+\eta)a^2
$$

would suffice without an adverse absolute-tail allowance. This comparison
is not established here for all those nodes. The opposite orientation
still requires quantitative control of the adverse residual; no assertion
that every node has the favorable orientation is made. At $a=0$, the
scalar inequality still does not supply $D_N+\mathcal R_N=b=0$ or
multiplicity propagation. This is a source-specific localization
application of the classical suppliers, with no literature novelty or
Lean proof claim; RH and all-integer strict Robin remain unproved.

## A single cutoff on a restricted source-parameter band

The same finite-series estimate gives a degree-independent threshold on
an explicitly restricted parameter range. Fix $\kappa>0$ and require
$v\ge\kappa n$; set

$$
r=\sqrt\kappa/2,\qquad \tau=\frac2{5\kappa},\qquad
\delta=\min(1/8,r/2),\qquad c=\pi e^{4r},\qquad d=c-\pi.
$$

Choose the same $\kappa$-dependent cutoff for every such $n,v$.
With $q,A,s$ as in (LC8), the finite series gives

$$
|q(T)|\le A e^{\tau T}\quad(T\ge0),\qquad
q(T)\ge A/2\quad(0\le T\le r^2). \tag{LC13}
$$

Here $2(n-1)/(5v)\le\tau$ and $\tau r^2=1/10$.
The lower bound (LC9) therefore remains valid with
$h=\min(r,M^{-2})$. The adverse integral has a bound involving only
a polynomial of degree four, rather than the degree-$n+1$ coefficient
sum in (LC10).

Indeed, $e^{4t}\ge1+4t+8t^2$ for $t\ge0$. If $8cM^2\ge\tau$,
then for every $m\ge M$,

$$
e^{\tau(r+t)^2}k_m(r+t)
\le2\pi^2m^4e^{9r+\tau r^2-cm^2}
                    e^{-(4cm^2-9-2\tau r)t}.
$$

Set $\widetilde\Lambda_M=4cM^2-9-2\tau r$. For
$\widetilde\Lambda_M>0$, integration against the remaining factor
$(r+t)^4$ gives

$$
\widetilde B_M=2\pi^2A e^{9r+\tau r^2}U_M(c)
 \sum_{\ell=0}^4\binom4\ell r^{4-\ell}
                         \frac{\ell!}{\widetilde\Lambda_M^{\ell+1}},
\qquad
s\mathcal R_N\ge\frac8{\xi_0}(L_M-\widetilde B_M). \tag{LC14}
$$

Define

$$
D=1-(3/2)^4e^{-5c},\qquad
G_4=\sum_{\ell=0}^4\binom4\ell r^{4-\ell}\ell!,\qquad
C_\kappa=\frac{40e^{9r+\tau r^2+4\pi(e-1)}G_4}{cD}.
$$

If

$$
M^2\ge\max\left(4,1/r,\frac\tau{8c},
                     \frac{9+2\tau r}{3c},\frac4d\right),
$$

then $\widetilde\Lambda_M\ge cM^2\ge1$ and the same comparison as
in (LC11) yields

$$
\frac{\widetilde B_M}{L_M}\le C_\kappa M^8e^{-dM^2}. \tag{LC15}
$$

All constants in (LC15) and the sufficient threshold depend only on
$\kappa$: the factor $A$ cancels from the ratio. A single strict test $C_\kappa M^8e^{-dM^2}<1$ therefore
certifies $s\mathcal R_N>0$ for every integer $n\ge1$, every
$v\ge\kappa n$, and every $N\ge M-1$, with this fixed cutoff.
Such an integer $M$ exists because the last bound decreases to zero.

At the actual nodes $v=n\lambda$, this covers the band
$\lambda\ge\kappa$; it supplies no uniform threshold as
$\lambda\downarrow0$. The favorable-orientation principal comparison
still has to hold for the same actual nodes and same splice, and the
opposite orientation and collision conditions retain their preceding
obligations. This restricted uniform error interface does not prove an
all-node Jensen estimate, RH, or all-integer strict Robin, and has not
been checked in Lean.

## Reusing compact Jensen convergence for the principal comparison

The local convergence mechanism is already classical:
[O'Sullivan, section 3.1, proof sketch following Theorem 3.1](https://arxiv.org/html/2007.13582v2#S3.SS1)
uses $g_n(F;z/n)\to F(z)$ locally uniformly. Its coefficient convention
and the repository's unchanged zero-shift normalization are recorded in
[the existing Jensen supplier](osullivan2021modifiedjensen.md) and
[the normalized source tower](../../Blueprint/D5/S3/Zeros/Jensen/NormalizedJensenDegreeLowering.md).
That convergence, its generic proof and the known finite-degree coverage
are reused; they are not additional mathematical results here.

For the same moments $M_k=\int T^k\,d\mu$ set
$a_k=4^kM_k/(2k)!$, $a_0=1$, and use the entire series

$$
f(t)=\Xi(\sqrt t)/\xi_0=\sum_{k\ge0}(-1)^ka_kt^k,
\qquad f_+(t)=\xi(1/2+\sqrt t)/\xi_0=\sum_{k\ge0}a_kt^k.
$$

The square-root notation names the even entire expansions. For $n\ge1$,
let $c_{n,k}=n^{\underline k}/n^k$ for $0\le k\le n$ and zero otherwise,
where $n^{\underline k}$ is the falling factorial. Write

$$
\mathcal J_n(t)=\sum_{k=0}^n(-1)^kc_{n,k}a_kt^k
=P_n^{\mathrm{source}}(-t),\qquad
\mathcal G_n(t)=\sum_{k=1}^{n+1}(-1)^kkc_{n,k-1}a_kt^{k-1}.
$$

The existing falling-factorial recurrence gives
$\mathcal J_{n+1}((1+1/n)t)-\mathcal J_n(t)=(t/n)\mathcal G_n(t)$.
At the unchanged original node $v=n\lambda>0$, $t=n/v=1/\lambda$,
require $\operatorname{sourceQ}_n(\lambda)=0$, equivalently
$\mathcal J_n(t)=0$. Then
the finite Laguerre series and the scale derivative and three-term
identities already used above give the parameter correspondence

$$
\beta a^2-ab
=(1/2)_{n-1}(1/2)_{n+1}v^{2n-2}
                \mathcal J_n'(t)\mathcal G_n(t). \tag{LC16}
$$

Here $(1/2)_j$ is the rising factorial. The prefactor is strictly positive;
(LC16) uses no division by $a$ and no simplicity assumption. It connects
the original principal comparison, rather than a changed measure or a
cutoff node, to two approximations of the same source derivative.

The positive coefficients give an explicit application of the classical
compact convergence. For fixed $R>0$ and $|t|\le R$,

$$
\begin{aligned}
|\mathcal J_n(t)-f(t)|&\le E_0/n,& E_0&=R^2f_+''(R)/2,\\
|\mathcal J_n'(t)-f'(t)|&\le E_1/n,& E_1&=(R^2f_+'''(R)+2Rf_+''(R))/2,\\
|\mathcal G_n(t)-f'(t)|&\le E_G/n,& E_G&=R^2f_+'''(R)/2.
\end{aligned} \tag{LC17}
$$

These coefficient budgets use $0\le1-c_{n,k}\le k(k-1)/(2n)$,
including the truncated tail, and the same bound with $k-1$ for
$\mathcal G_n$. No additional source or generic convergence theorem
is introduced.

Suppose all real zeros of $f$ in $I=[0,R]$ are simple, and supply relative
open neighborhoods $U$ of those zeros and finite separation inputs $c,m>0$
with $|f|\ge c$ on $I\setminus U$ and $|f'|\ge m$ on $U$. Then

$$
n>\max\{E_0/c,E_1/m,E_G/m\} \tag{LC18}
$$

places every real $\mathcal J_n$ node in $I$ inside $U$ and makes
$\mathcal J_n'$ and $\mathcal G_n$ have the same nonzero sign as $f'$
at those nodes.
The margin in (LC16) is strictly positive in both residual orientations,
and $a\ne0$ there. If $f$ has no zeros in $I$, only $E_0/c$ is needed
and there are no nodes in that band. This is a conditional application
of the cited convergence, not an assertion of source-zero simplicity.

The same source also gives a relative principal-margin budget without
separating the finite part from its residual. Define

$$
h_n(t)=\sum_{k=0}^nc_{n,k}
             \frac{M_{k+1}}{k!(1/2)_k}(-t)^k,\qquad
B_R=Rf_+''(R)+\tfrac12f_+'(R)>0.
$$

The finite Laguerre coefficients give, at these unchanged nodes,

$$
\frac{b}{\beta a}=\frac{h_n(t)}{n\mathcal J_n'(t)},\qquad
|h_n(t)|\le
\sum_{k\ge0}\frac{M_{k+1}R^k}{k!(1/2)_k}=B_R. \tag{LC19}
$$

Here $a\ne0$ follows from the already stated source separation and (LC17).
Thus, with $\epsilon_n=B_R/(nm-E_1)$,

$$
\left|\frac{b}{\beta a}\right|\le\epsilon_n,\qquad
\beta a^2-ab\ge(1-\epsilon_n)\beta a^2,\qquad
aD_N+a\mathcal R_N\le(\eta+\epsilon_n\beta)a^2. \tag{LC20}
$$

The last inequality keeps the same splice and its nonzero node residual:
$D_N+\mathcal R_N=b+\eta a$ by (LC6); $c_H$ is not dropped.
The additional condition $nm\ge E_1+2B_R$ gives
$\epsilon_n\le1/2$, hence a positive relative margin in both orientations.
This bounds the total correlation. An available lower bound on a favorable
residual cannot be substituted for its actual value in an upper bound
for the finite part.

The range is $\lambda\ge1/R$ above a source-dependent degree threshold.
No numerical $c,m$ or threshold is supplied. Degrees below it, source
multiplicities and uniform control as $R\to\infty$ are not settled by
this application. Existing finite certificates are cited directly in the
Jensen supplier, without rerunning them. No new Lean declaration,
originality claim, all-node estimate, RH or all-integer Robin proof
follows from (LC16)–(LC20).


## Why the compact positive-coefficient budget cannot cover every node

The fixed coefficient of the normalized source tower and the classical
root–coefficient identity give a limitation of (LC18)–(LC20).
This is a parameter application, not a new Viète theorem or a conclusion
that the actual node inequality fails.

For an integer $n\ge1$, suppose the unchanged polynomial
$q_n(\lambda)=\lambda^n\mathcal J_n(1/\lambda)$ has $n$ positive roots
$\lambda_i$, counted with multiplicity. Its leading two coefficients
are $1,-a_1$, by the
[existing source normalization](../../Blueprint/D5/S3/Zeros/Jensen/NormalizedJensenDegreeLowering.md).
Viète's identity, also supplied by Mathlib's
`Polynomial.Splits.nextCoeff_eq_neg_sum_roots_of_monic`,
therefore gives

$$
\sum_{i=1}^n\lambda_i=a_1,\qquad
\max_i(1/\lambda_i)\ge n/a_1. \tag{LC21}
$$

Thus any one interval $[0,R]$ containing all these actual reciprocal
nodes must have $R\ge n/a_1$.

Fix a positive real zero $t_*$ of the same $f$ and put
$M=|f'(t_*)|<\infty$. Once $R\ge t_*$, the separation data in (LC18)
require $t_*\in U$ and $0<m\le M$. If $M=0$, such data cannot exist.
Both $M$ and the positive source coefficients $a_1,a_3$ are independent
of the polynomial degree.

The already used positive entire series, retaining just its $a_3$ term,
gives

$$
E_1(R)\ge9a_3R^2,\qquad
B_R\ge\tfrac{15}{2}a_3R^2. \tag{LC22}
$$

If $R\ge t_*$, all reciprocal nodes are covered and the separation data
in (LC18) exist, then $M>0$ and (LC18) requires
$n<Ma_1^2/(9a_3)$. Under those same separation and coverage assumptions,
the (LC20) half-margin condition $nm\ge E_1(R)+2B_R$ requires
$n\le Ma_1^2/(24a_3)$. Indeed, the applicable budgets obey

$$
9a_3n^2/a_1^2\le E_1(R)<nm\le nM,
\qquad
24a_3n^2/a_1^2\le E_1(R)+2B_R\le nm\le nM.
$$

These are finite certificate caps, not numerical values for the actual
source. They use $R\ge t_*$; before that inclusion, $m\le M$ is unavailable.

Assuming such a fixed positive source zero $t_*$ exists, no unbounded set
of degrees with $n$ positive roots can admit these single-interval
certificates. For every $n\ge a_1t_*$, all-node coverage forces
$R_n\ge t_*$. Whenever separation data exist, the same $M$ bounds every
$m_n$, even if $R_n,U_n,m_n$ vary with $n$. If $M=0$, those separation
data are impossible. This obstruction leaves multiple local certificates,
fixed-band applications, cancellation-sensitive estimates, the weaker
margin goal and the underlying sign/RH/Robin goals undecided. The
calculation is ordinary analysis, with no new Lean declaration or
originality claim.



## Multiple real source zeros on a fixed band

The arbitrary-center Poisson–Charlier bound in
[Zacharovas, Theorem 2.8](zacharovas2025depoissonization.md)
provides a local application beyond the simple-source-zero premise in
(LC18). The source, coefficients and actual nodes in (LC16) are unchanged.
The following is a parameter application of that bound, classical
Charlier–Hermite convergence and compact Jensen convergence; none of
those general results is reproved or claimed as new.

For the same $n,t>0$, put $\alpha=t/n$ and
$g_s(z)=f^{(s)}(\alpha z)$, $s=0,1$. The existing coefficient
normalization gives

$$
\begin{aligned}
n![z^n]e^zg_0(z)&=\mathcal J_n(t),\\
n![z^n]e^zg_1(z)&=\mathcal G_n(t),\\
(n-1)![z^{n-1}]e^zg_1(z)&=\mathcal J_n'(t).
\end{aligned} \tag{LC23}
$$

The real coefficients and entire exponential generating functions meet
the supplier's assumptions. Their absolute Poisson averages satisfy
$\mathscr E(g_s^{(j)};\rho)\le
\alpha^j f_+^{(s+j)}(\alpha\rho)$.
The auxiliary functions only extract the original coefficients; they do
not replace the original measure or impose a Laguerre–Polya/RH premise.

Fix a positive real source zero $\tau$ of finite multiplicity $r\ge1$,
and let $A_\tau=f^{(r)}(\tau)/r!\ne0$. Set

$$
t=\tau(1+x/\sqrt n),\qquad u=1+x/\sqrt n>0,\qquad
\rho=n/u,\qquad
Q_\tau=\frac{\tau f_+^{(r+1)}(\tau)}{|A_\tau|},
\quad
W_\ell(\rho)=\frac{\ell!e^\rho}{\rho^\ell\sqrt\ell}.
$$

Thus $\alpha\rho=\tau$. For $n\ge3$, apply the supplier with
$(\ell,N,s)=(n,r,0),(n,r-1,1),(n-1,r-1,1)$. The lower derivatives
vanish at the same source zero, giving

$$
\begin{aligned}
\mathcal J_n(t)&=A_\tau\tau^r\mathsf C_r(\rho,n)+e_0,\\
\mathcal G_n(t)&=rA_\tau\tau^{r-1}\mathsf C_{r-1}(\rho,n)+e_V,\\
\mathcal J_n'(t)&=rA_\tau\tau^{r-1}\mathsf C_{r-1}(\rho,n-1)+e_D,
\end{aligned} \tag{LC24}
$$

with the supplier's finite-degree remainder bounds

$$
\begin{aligned}
\left|\frac{n^{r/2}e_0}{A_\tau\tau^r}\right|
&\le \frac{12Q_\tau}{\sqrt n}W_n(\rho)u^{r+1},\\
\left|\frac{n^{(r-1)/2}e_V}{A_\tau\tau^{r-1}}\right|
&\le \frac{12Q_\tau}{\sqrt n}W_n(\rho)u^r,\\
\left|\frac{n^{(r-1)/2}e_D}{A_\tau\tau^{r-1}}\right|
&\le \frac{12Q_\tau}{\sqrt n}W_{n-1}(\rho)
                 (1-1/n)^{r/2}u^r.
\end{aligned} \tag{LC25}
$$

The source's Stirling bound gives
$W_\ell(\rho)\le e\exp(\rho-\ell-\ell\log(\rho/\ell))$.
For fixed $\tau,r,L$ and $|x|\le L$, these errors are
$O_{\tau,r,L}(n^{-1/2})$.

Use $\operatorname{He}_r(x)=2^{-r/2}H_r(x/\sqrt2)$. In the supplier's
normalization, [DLMF 18.21.9](https://dlmf.nist.gov/18.21.E9)
and its fixed-degree finite-sum formula give, uniformly for $|x|\le L$,

$$
\begin{aligned}
F_n(x)&=\frac{n^{r/2}\mathcal J_n(t)}{A_\tau\tau^r}
          =\operatorname{He}_r(x)+O_{\tau,r,L}(n^{-1/2}),\\
D_n(x)&=\frac{n^{(r-1)/2}\mathcal J_n'(t)}{A_\tau\tau^{r-1}}
          =F_n'(x)=\operatorname{He}_r'(x)+O_{\tau,r,L}(n^{-1/2}),\\
V_n(x)&=\frac{n^{(r-1)/2}\mathcal G_n(t)}{A_\tau\tau^{r-1}}
          =\operatorname{He}_r'(x)+O_{\tau,r,L}(n^{-1/2}).
\end{aligned} \tag{LC26}
$$

The derivative convention also uses
[DLMF 18.9.25](https://dlmf.nist.gov/18.9.E25).
For finite-degree use, each error in (LC26) is bounded by the
corresponding explicit normalized Charlier polynomial's error on
$[-L,L]$, plus (LC25); the asymptotic notation is not a numerical
certificate.

Let $h_1<\cdots<h_r$ be the real simple Hermite zeros. Choose disjoint
closed intervals $I_j$ around them, contained in $[-L,L]$, with

$$
m_*=\min_{\cup_jI_j}|\operatorname{He}_r'|>0,\qquad
q_*=\min_{\cup_j\partial I_j}|\operatorname{He}_r|>0.
$$

Write $\delta_0,\delta_D,\delta_V$ for the suprema of the three errors
in (LC26) on $[-L,L]$. Also choose a fixed complex disk
$B(\tau,d)$, $0<d<\tau$, containing no other source zero, and
$\gamma_\tau=\min_{|z-\tau|=d}|f(z)|>0$.
The joint sufficient conditions are

$$
\delta_0<q_*,\quad
\delta_D<m_*/2,\quad \delta_V<m_*/2,\quad
\tau L/\sqrt n<d,\quad
E_0(\tau+d)/n<\gamma_\tau. \tag{LC27}
$$

The last condition applies (LC17) on the complex circle; classical
Rouché counting gives exactly $r$ polynomial zeros in the disk, counted
with multiplicity. The first three conditions give a unique real simple
zero in each $I_j$: the endpoint signs persist and $D_n$ has a fixed
nonzero sign there. The fourth places those roots inside the disk, so
they account for its entire zero count. At each of these actual
$\mathcal J_n$ nodes,

$$
\mathcal J_n'(t)\mathcal G_n(t)
\ge A_\tau^2\tau^{2r-2}n^{-(r-1)}m_*^2/4>0. \tag{LC28}
$$

All conditions in (LC27) hold eventually for fixed $\tau,r,L,d$.
No simplicity of the source zero is assumed. This count and sign concern
the exact polynomial nodes, not merely values at the limiting Hermite
zeros. The existing lowering and adjacent-row identities then exclude
the two relevant common zeros at the same original $v$:

$$
\mathcal J_{n-1}((1-1/n)t)=-t\mathcal J_n'(t)/n\ne0,\qquad
\mathcal J_{n+1}((1+1/n)t)=t\mathcal G_n(t)/n\ne0.
$$

Thus (LC16) gives $\beta a^2-ab>0$ and $a\ne0$ on these clusters.

The relative correlation also keeps the local cancellation. The existing
coefficients in (LC19) give
$h_n=-t\mathcal G_n'-\mathcal G_n/2$ and
$\mathcal J_n'=\mathcal G_n-(t/n)\mathcal G_n'$. Hence at these nodes

$$
\frac b{\beta a}
=1-\left(1+\frac1{2n}\right)\frac{\mathcal G_n}{\mathcal J_n'},\qquad
\left|\frac b{\beta a}\right|
\le\frac1{2n}
+\left(1+\frac1{2n}\right)
\frac{\delta_D+\delta_V}{m_*-\delta_D}
=:\epsilon_{\tau,n}
=O_{\tau,r,L}(n^{-1/2}). \tag{LC29}
$$

The original splice therefore still satisfies
$aD_N+a\mathcal R_N\le(\eta+\epsilon_{\tau,n}\beta)a^2$ in both residual
orientations, with its nonzero approximating-node residual retained.
This uses the correlated three-row estimate instead of dividing the
absolute $B_R$ budget by a vanishing source derivative.

For every fixed $R>0$, the source has finitely many real zeros in a
slightly larger fixed interval, each of finite multiplicity since
$f(0)=1$. Apply the cluster construction at each one. Away from their
neighborhoods, compact Jensen convergence and a positive $|f|$ floor
exclude additional real nodes. If $R$ itself is a source zero, retain
its whole cluster using the larger interval. Consequently there are
source-dependent $N_R,C_R$ such that

$$
n\ge N_R,\quad 0<t\le R,\quad\mathcal J_n(t)=0
\ \Longrightarrow\
\mathcal J_n'(t)\mathcal G_n(t)>0,\quad a\ne0,\quad
|b/(\beta a)|\le C_R/\sqrt n. \tag{LC30}
$$

Source zeros off the real axis are allowed throughout. This does not
establish real-rootedness of the whole polynomial. Fixed-band
large-degree collisions are excluded by (LC30); low-degree or unbounded
height collisions still need the original vanishing and multiplicity
propagation arguments.

The quantifiers remain $\forall R\,\exists N_R$, with no numerical
threshold supplied. A moving-height use must jointly control (LC25),
the finite Charlier errors and Hermite margins, isolation radii and
circle floors in (LC27), and a source floor outside all captured
clusters. It must additionally cover every actual positive node by
$R_n$ or supply an estimate beyond it. A slowly growing chosen band
does not by itself establish that coverage; (LC21) already requires
$R_n\ge n/a_1$ in degrees with all $n$ roots positive.
No uniform high-height estimate, new Lean declaration, originality
claim, RH or all-integer Robin proof is supplied by this application.


## A mandatory node scale from the existing xi coefficient asymptotic

The original normalized source has $a_k=\Gamma_k/(\xi_0 k!)$,
with the unchanged positive $\Gamma_k$ of O'Sullivan's (1.2).
Write $w_n=W(2n/\pi)$ and $r_n=a_{n-1}/a_n$.
[O'Sullivan, Theorem 1.4](https://arxiv.org/html/2007.13582v2#S1.Thmtheorem4)
with $K=1$, applied at $n,n-1$, gives

$$
r_n=\frac{n\Gamma_{n-1}}{\Gamma_n}
=\frac{16n^2}{w_n^2}
  \left(1+O\!\left(\frac{\log n}{n}\right)\right). \tag{LC31}
$$

This directly reuses the published coefficient asymptotic, with no
new saddle-point theorem or numerical coefficient computation.
For the normalization check, let

$$
D(x)=4\pi^2e^{7w(x)/4}\sqrt{\frac{w(x)}{w(x)+1}}
\left(\frac{e\,w(x)^2}{16x e^{2/w(x)}}\right)^x,
\qquad w(x)=W(2x/\pi).
$$

The supplier says $\Gamma_n=D(n)(1+O(\log n/n))$.
Differentiating its explicit leading term with
$w'(x)=w(x)/(x(1+w(x)))$ yields

$$
\frac{d}{dx}\log D(x)=
\log\frac{w(x)^2}{16x}+O(1/x).
$$

Thus $D(n-1)/D(n)=(16n/w_n^2)(1+O(1/n))$;
the published relative errors supply (LC31). The estimate is asymptotic,
not an explicit finite-degree threshold.

Now suppose $\mathcal J_n$ has $n$ positive real roots $t_i$, counted
with multiplicity. Its last two coefficients are
$(-1)^n(n!/n^n)a_n$ and
$(-1)^{n-1}(n!/n^{n-1})a_{n-1}$.
The classical root–coefficient identity gives

$$
\sum_{i=1}^nt_i=nr_n,\qquad
r_n\le t_{\max}\le nr_n. \tag{LC32}
$$

Consequently, along any unbounded set of such complete positive-root
degrees, a single all-node band must satisfy

$$
R_n\ge r_n\sim\frac{16n^2}{W(2n/\pi)^2}.
$$

For the original node parameters $v_i=n/t_i$ and $\lambda_i=1/t_i$,

$$
\frac1{r_n}\le \min_i v_i\le\frac n{r_n},
\qquad
\frac1{nr_n}\le\min_i\lambda_i\le\frac1{r_n}. \tag{LC33}
$$

In particular, along those degrees $\min_i v_i\to0$ and
$\min_i\lambda_i\to0$; the upper bounds are asymptotic to
$W(2n/\pi)^2/(16n)$ and $W(2n/\pi)^2/(16n^2)$, respectively.
This identifies a compulsory small-$v$ range absent from fixed-$v$
asymptotics and from fixed positive $v/n$ cutoff bands.

The complete positive-root premise is explicit. These are bounds on the
actual node heights, not proof that every degree has those roots, not a
sign estimate at the nodes and not RH/Robin. Only the existing supplier
and Viète are used; the parameter application is ordinary analysis,
with no new Lean declaration or originality claim.


## An all-node enclosure without a hyperbolicity premise

The original coefficient normalization also permits a direct application
of classical Eneström–Kakeya. For its positive nondecreasing-coefficient
form, see Ramulu and Reddy, *On the Eneström Kakeya Theorem*,
[Theorem (A1), printed p.688](https://www.ijpam.eu/contents/2015-102-4/8/8.pdf),
*International Journal of Pure and Applied Mathematics* **102** (2015),
687–700, DOI [10.12732/ijpam.v102i4.8](https://doi.org/10.12732/ijpam.v102i4.8).
Only the classical theorem recalled there is used; none of that paper's
new generalizations is needed.

[O'Sullivan's (1.5)](https://arxiv.org/html/2007.13582v2) reports the
coefficient Turán inequality, proved for all indices by Csordas, Norfolk
and Varga, *The Riemann hypothesis and the Turán inequalities*,
*Transactions of the American Mathematical Society* **296** (1986),
521–541, DOI [10.2307/2000378](https://doi.org/10.2307/2000378):
$\Gamma_{j+1}^2\ge\Gamma_j\Gamma_{j+2}$ for every $j\ge0$.
This is the original $\Gamma_j$ convention already used in (LC31),
not the ordinary Taylor coefficients with their factorial removed.
The published inequality is reused; its proof is not repeated here.

For $n\ge1$, write

$$
B_n(z)=\mathcal J_n(-z)=\sum_{k=0}^nb_{n,k}z^k,
\qquad b_{n,k}=c_{n,k}a_k>0,
\qquad r_k=\frac{a_{k-1}}{a_k}
       =\frac{k\Gamma_{k-1}}{\Gamma_k}.
$$

The published coefficient inequality gives
$r_k/k\ge r_{k-1}/(k-1)$ for $k\ge2$.
Consequently $r_k$ increases, and the adjacent coefficient ratios are

$$
\frac{b_{n,k-1}}{b_{n,k}}
=\frac{n r_k}{n-k+1},\qquad
\min_{1\le k\le n}\frac{b_{n,k-1}}{b_{n,k}}=r_1,
\qquad
\max_{1\le k\le n}\frac{b_{n,k-1}}{b_{n,k}}=n r_n. \tag{LC34}
$$

The positive coefficients of $B_n(nr_n z)$ are nondecreasing.
Those of $z^nB_n(r_1/z)$, written in increasing powers of $z$, are
also nondecreasing. Applying the cited classical theorem to these two
polynomials supplies, for every complex zero of the actual row,

$$
\mathcal J_n(t)=0
\quad\Longrightarrow\quad
r_1=\frac1{a_1}\le |t|\le n r_n. \tag{LC35}
$$

No real-rootedness, simplicity or RH hypothesis is used in this enclosure.
In particular every actual positive node obeys

$$
\frac1{nr_n}\le\lambda=\frac1t\le a_1,
\qquad
\frac1{r_n}\le v=\frac nt\le n a_1. \tag{LC36}
$$

Reuse (LC31) for the upper endpoint
$nr_n\sim16n^3/W(2n/\pi)^2$.
Thus $[r_1,nr_n]$ is a degree-dependent all-positive-node band available
without the complete positive-root premise of (LC32). It is an enclosure,
not an assertion that either endpoint is attained or that the actual
largest node is asymptotic to that upper endpoint.

The signed comparison $\mathcal J_n'(t)\mathcal G_n(t)\ge0$ must still
be established at every actual positive node in this growing band, with
the original additional vanishing and multiplicity obligations at
collisions. The enclosure provides no error, derivative floor, separation
or signed margin there. Neither it nor the fixed-band result (LC30)
supplies a uniform conclusion on $[r_1,nr_n]$. This is an application of
published results to the unchanged source, with no new Lean declaration,
originality claim, RH or all-integer Robin proof.


## A conditional second-moment enclosure on the mandatory scale

Reuse the unchanged normalization $a_k=\Gamma_k/(\xi_0 k!)$ and
$r_n=a_{n-1}/a_n$ of (LC31). Griffin, Ono, Rolen, Thorner, Tripp and
Wagner, [*Jensen polynomials for the Riemann xi-function*,
arXiv:1910.01227v3](https://arxiv.org/html/1910.01227v3), use the same
$\Gamma_k=\gamma(k)$ in (1.1)–(1.2). Their (2.3) and Theorem 2.1(1)
give, without RH or whole-row hyperbolicity,

$$
\Delta(n)^2=\frac12\left(1-
\frac{\Gamma_{n-2}\Gamma_n}{\Gamma_{n-1}^2}\right),
\qquad \Delta(n)\sim\frac1{\sqrt{2n}}.
$$

The theorem numbering here refers to that arXiv version. Its
$C$-dependent threshold $M_C$ is existential, not a numerical cutoff.
For $n\ge3$, the factorial correspondence gives

$$
d_n:=n\left(1-\frac{a_{n-2}a_n}{a_{n-1}^2}\right)
=1+2(n-1)\Delta(n)^2\longrightarrow2. \tag{LC37}
$$

This second-order information is taken directly from the supplier;
it is not inferred by subtracting the first-order remainder in (LC31).

Suppose now that this actual row $\mathcal J_n$ has all $n$ roots
$t_i>0$, counted with multiplicity. No assumption about another row
is made. The last three positive coefficient magnitudes are

$$
b_{n,n}=\frac{n!}{n^n}a_n,\qquad
b_{n,n-1}=\frac{n!}{n^{n-1}}a_{n-1},\qquad
b_{n,n-2}=\frac{n!}{2n^{n-2}}a_{n-2}.
$$

Apply the classical root–coefficient identities
([DLMF (1.11.10), §1.11(ii)](https://dlmf.nist.gov/1.11.E10)) to these same roots:
$\sum_i t_i=nr_n$ and
$\sum_{i<j}t_it_j=(n^2/2)a_{n-2}/a_n$. Hence

$$
\sum_{i=1}^nt_i^2=nd_nr_n^2,\qquad
\frac1n\sum_{i=1}^n(t_i-r_n)^2=(d_n-1)r_n^2. \tag{LC38}
$$

Since $t_i^2\le t_{\max}t_i$ and
$t_{\max}^2\le\sum_i t_i^2$, the complete positive-root premise gives

$$
d_nr_n\le t_{\max}\le r_n\sqrt{nd_n}. \tag{LC39}
$$

Together with (LC31) and (LC37), along any unbounded set of such degrees,

$$
t_{\max}\ge(32+o(1))\frac{n^2}{W(2n/\pi)^2},\qquad
t_{\max}\le(16\sqrt2+o(1))\frac{n^{5/2}}{W(2n/\pi)^2}.
$$

The upper bound is conditional on this row's positive roots; it cannot
replace the unconditional complex-root enclosure (LC35). Neither bound
is an asymptotic equality for the largest root.

The same empirical law on these $n$ actual roots supplies a proportion
bound. For $0<\theta<1$ and $B>\theta$, apply finite Cauchy–Schwarz
and the second-moment Markov bound using (LC38):

$$
(1-\theta)nr_n
\le\sum_{t_i\ge\theta r_n}t_i
\le\sqrt{\#\{i:t_i\ge\theta r_n\}\,nd_nr_n^2},
\qquad
\frac{\#\{i:t_i>Br_n\}}n\le\frac{d_n}{B^2}.
$$

Consequently,

$$
\frac{\#\{i:\theta r_n\le t_i\le Br_n\}}n
\ge\frac{(1-\theta)^2}{d_n}-\frac{d_n}{B^2}. \tag{LC40}
$$

Both bounds concern the same complete row and count multiplicities;
no separately optimized distributions are combined. In particular,

$$
\frac{\#\{i:r_n/2\le t_i\le8r_n\}}n
\ge\frac1{4d_n}-\frac{d_n}{64}
\longrightarrow\frac3{32}\quad\text{on the right-hand side}. \tag{LC41}
$$

Thus along any unbounded set of complete positive-root degrees, the
liminf of the fraction in this band is at least $3/32$. This is not a
claim that the actual fraction converges to that value, or that the
nodes are distinct. The original parameters of each node in the band are

$$
\frac{n}{8r_n}\le v=\frac nt\le\frac{2n}{r_n},\qquad
\frac1{8r_n}\le\lambda=\frac1t\le\frac2{r_n}. \tag{LC42}
$$

By (LC31), the two $v$ endpoints are asymptotic respectively to
$W(2n/\pi)^2/(128n)$ and $W(2n/\pi)^2/(8n)$, and both tend to zero.
Under the explicit row premise, a fixed positive $v$ regime therefore
misses a positive proportion of the original nodes, not merely one
possible outlier. No numerical starting degree is supplied.

These are parameter applications of published coefficient results and
classical root and moment inequalities, with no new generic theorem,
Lean declaration or originality claim. The positive-root premise is
not established by (LC37). The moments supply no separation, derivative
floor, adjacent-row signed margin or collision propagation on this band.
The all-height signed comparison and RH/all-integer Robin remain unresolved.


## A conditional full-row zero law from the finite S-transform

Reuse (LC31) and the unchanged actual coefficients. Arizmendi, Fujie,
Perales and Ueda, [*S-transform in finite free probability*,
arXiv:2408.09337v2](https://arxiv.org/html/2408.09337v2),
Definition 6.1 and Theorem 1.1, characterize weak empirical-root
convergence for polynomials with all roots nonnegative by diagonal
limits of their finite $S$-transforms. Proposition 7.9 allows a
sequence of degrees tending to infinity rather than every degree.
Example 10.10 identifies $S_{\mathrm{MP}_1}(-u)=1/(1-u)$.
The general theorem is reused, not proved again.

For the actual row define its monic normalization

$$
p_n(x)=\frac{(-1)^nn^n}{n!\,a_nr_n^n}\mathcal J_n(r_nx)
=\sum_{k=0}^n(-1)^k\binom nk\widetilde e_k(p_n)x^{n-k}.
$$

Matching the original coefficients gives

$$
\widetilde e_k(p_n)
=\frac{n^k}{n^{\underline k}r_n^k}\frac{a_{n-k}}{a_n},
\qquad
\frac{\widetilde e_{k-1}(p_n)}{\widetilde e_k(p_n)}
=\frac{n-k+1}{n}\frac{r_n}{r_{n-k+1}}. \tag{LC43}
$$

The coefficient identity requires no root assumption. To apply the
supplier, suppose $n_j\to\infty$ and each actual $\mathcal J_{n_j}$
has all $n_j$ roots positive real, counted with multiplicity.
No premise about an adjacent row or the whole source is added.
For every sequence $1\le k_j\le n_j$ with $k_j/n_j\to u\in(0,1)$
on these same complete actual positive-root rows, (LC31) gives
$r_{n_j-k_j+1}/r_{n_j}\to(1-u)^2$: the Lambert $W$ ratio tends
to one when its arguments have a fixed positive limiting ratio.
Consequently (LC43) is the finite $S$-transform under this premise,
and tends to $1/(1-u)$. The supplier yields

$$
\frac1{n_j}\sum_{\mathcal J_{n_j}(t_i)=0}
 \delta_{t_i/r_{n_j}}\ \Longrightarrow\ \mathrm{MP}_1,
\qquad
d\mathrm{MP}_1(x)=\frac1{2\pi}\sqrt{\frac{4-x}{x}}\,
                    \mathbf1_{(0,4)}(x)\,dx. \tag{LC44}
$$

This does not establish the existence of an unbounded sequence of
complete positive-root rows. It is a conditional application of a
published general theorem, not a new generic zero-distribution theorem.

The limiting measure has no atoms. Its distribution function on $[0,4]$ is

$$
C(x)=\frac2\pi\arcsin\sqrt{x/4}
       +\frac1{2\pi}\sqrt{x(4-x)}.
$$

Thus, along the same complete positive-root subsequence, the fraction
in the band of (LC41) actually has the conditional limit

$$
\frac{\#\{i:r_{n_j}/2\le t_i\le8r_{n_j}\}}{n_j}
\longrightarrow
1-\frac2\pi\arcsin\frac1{\sqrt8}-\frac{\sqrt7}{4\pi}. \tag{LC45}
$$

For these actual nodes the original $v,\lambda$ intervals remain
exactly (LC42). No node has been replaced by a model root.
The sharper proportion uses the full diagonal coefficient profile,
rather than repeating the two-moment calculation.
More generally, along this same complete actual positive-root
subsequence and counting multiplicities, the normalized root fractions
in every fixed interval converge to the corresponding
$\mathrm{MP}_1$ mass. This is weak
convergence with no supplied rate. The limit's support $[0,4]$ does
not put every finite-row root in $[0,4+o(1)]$, exclude $o(n)$ outliers,
or prove $t_{\max}/r_n\to4$. Neither simplicity, separation nor the
same-node adjacent-row sign follows from it.


## The complete Appell supplier and the unchanged adjacent node

Campbell and Jalowy, [*Pólya–Schur problems and free probability*,
arXiv:2605.31356v1](https://arxiv.org/html/2605.31356v1),
Theorem 4.4, give complete Appell asymptotics with any fixed integer
degree offset $d$, uniformly on compact bulk sets. Theorem 2.7
states a local cosine phase for fixed nonnegative offsets, uniformly
for bounded microscopic displacement. These concern large degree,
including adjacent degrees, rather than a fixed degree with a large
coefficient shift.

Their (1.4) and (1.6) use
$A_{m,f}(y)=f(\partial_y)y^m$ and $A_{m,f}'=mA_{m-1,f}$.
The finite coefficient formula makes sense for any entire $f$;
using it alone does not assert membership in their source class.
Let

$$
F(z)=\frac{\Xi(\sqrt z)}{\xi_0}
     =\sum_{k\ge0}(-1)^ka_kz^k,\qquad
f_n(z)=F((r_n/n)z),\qquad y=r_n/t>0.
$$

The square root denotes the even entire power series. Directly
matching the finite operator coefficients, for fixed integer $d$
and $n+d\ge1$, gives

$$
A_{n+d,f_n}(y)
=y^{n+d}\mathcal J_{n+d}
       \left(\frac{n+d}{n}\frac{r_n}{y}\right). \tag{LC46}
$$

Here every offset uses the same source $f_n$, not $f_{n+d}$.
For $d=0,1$, at the same $y=r_n/t$, the two arguments are exactly
$t$ and $(1+1/n)t$. On the actual node $\mathcal J_n(t)=0$,
the already established adjacent identity and Appell differentiation give

$$
A_{n-1,f_n}(y)=-\frac{r_ny^{n-2}}n\mathcal J_n'(t),
\qquad
A_{n+1,f_n}(y)=\frac{r_ny^n}n\mathcal G_n(t).
$$

Consequently the unpaid comparison has the exact same-node form

$$
\mathcal J_n'(t)\mathcal G_n(t)
=-\frac{n^2}{r_n^2y^{2n-2}}
       A_{n-1,f_n}(y)A_{n+1,f_n}(y),
\qquad
\mathcal J_n'(t)\mathcal G_n(t)\ge0
\iff A_{n-1,f_n}(y)A_{n+1,f_n}(y)\le0. \tag{LC47}
$$

This identity requires no simplicity assumption. It does not prove
the sign, rule out common zeros or propagate their multiplicities.
For fixed $0<a\le t/r_n\le b<\infty$, the corresponding $y$ is in
the fixed compact interval $[1/b,1/a]$. This establishes only the
parameter correspondence. It does not establish membership in
Theorem 4.4's real bulk set
$-\infty<\operatorname{Im}G_{\mu_{c,\Sigma}}(y+i0)<0$,
Theorem 2.7's bounded-density condition, or the squared-source
$\mathcal{LP}_{M_n}$ and Assumption A hypotheses.

The applicability obligation is different. Their (1.1) defines
$\mathcal{LP}_M$ by a real entire canonical product whose every zero
lies in the horizontal strip $|\operatorname{Im}z|\le M$.
Assumption A requires $f_n\in\mathcal{LP}_{M_n}$ with $M_n=o(n)$,
the weighted reciprocal-root measure convergence in (2.2), and the
drift convergence in (2.3).
Those source conditions have not been established here for the
actual $f_n=F((r_n/n)z)$.

The known $\Xi$ strip does not discharge the first condition.
If $u+iv$ is a $\Xi$ zero, $|v|\le1/2$, its squared-source zero is
$z=(u+iv)^2$. The strip implies only the parabolic enclosure

$$
(\operatorname{Im}z)^2=4u^2v^2
\le u^2=\operatorname{Re}z+v^2
\le\operatorname{Re}z+\tfrac14. \tag{LC48}
$$

It supplies no finite global horizontal width for $F$.
This is a limit of the known enclosure, not an assertion that
nonreal $\Xi$ zeros exist, nor that a weaker source-specific
extension of the supplier is impossible. A single positive-root
row cannot be substituted for the entire-source hypotheses.

The paper's Corollary 2.4 does give an unconditional Cauchy zero law
for the classical $\Xi(2z/\log n)$ Appell/Jensen rows. It is not a
zero law for (LC46). Before that scalar rescaling, the even
classical Jensen row has coefficients
$(-1)^k(2n)^{\underline{2k}}a_kz^{2k}$.
After squaring the variable its weights still differ from the
actual $\mathcal J_n$ weights:

$$
(2n)^{\underline{2k}}
=4^k n^{\underline k}(n-\tfrac12)^{\underline k}.
$$

The last falling-factorial factor depends on $k$ and cannot be
removed by a constant variable scaling. Therefore the Cauchy
corollary cannot be transferred to (LC44) by squaring zeros.

Even if Assumption A were paid, a signed use at actual zeros must
control the simultaneous offset errors relative to a nonzero
adjacent-product margin. The printed real-bulk formula (4.14)
places a $(1+o(1))$ after twice a real part; it cannot be used as
a relative-error certificate at a cancellation of that real part.
The proof treats two conjugate saddle contributions separately.
An application must justify the required common-envelope absolute
error there, and retain edge and common-zero obligations, rather
than infer them from the displayed cosine or a weak zero law.

These are existing-source parameter correspondences and conditional
applications, with no new Lean declaration or originality claim.
No complete squared-source asymptotic, all-node signed comparison,
RH proof or strict all-integer Robin proof is supplied here.


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


## A Gamma–zeta contour for the actual square-variable source

Keep the original coefficients, $r_n$, $F$, $f_n$, and $A_{m,f_n}$
of (LC31) and (LC46). In particular, $F(z)=\Xi(\sqrt z)/\xi_0$
is the square-variable source; it is not the square of $\Xi$.
Let $\omega_n=\sqrt{r_n}$. The existing coefficient asymptotic gives

$$
\omega_n\sim\frac{4n}{W(2n/\pi)},\qquad
\frac{\omega_n}{n}\longrightarrow0,\qquad
\frac{\omega_n\log\omega_n}{2n}\longrightarrow2. \tag{LC49}
$$

The suppliers used below are classical and are reused directly:
[DLMF (25.4.3)–(25.4.4)](https://dlmf.nist.gov/25.4) for the
reflection and Gamma–zeta formula for $\xi$, its
[Dirichlet series (25.2.1)](https://dlmf.nist.gov/25.2), and the
uniform sectorial Stirling expansion
[(5.11.1)](https://dlmf.nist.gov/5.11).
For the integral remainder use O'Sullivan,
[*Revisiting the saddle-point method of Perron*,
arXiv:1702.03777v2](https://arxiv.org/abs/1702.03777v2),
Corollary 5.1, printed p.15, with $\mu=2,M=1$.
The paper explicitly makes the error constant independent of
its holomorphic amplitude, bounded by $K_q$ on the fixed
neighborhood and contour. Assumptions 1.1 require a fixed phase.
After the exact local change of variable below, the application
uses the fixed phase $-\tau^2/2$, on a fixed segment $[-\beta,\beta]$,
with a uniformly bounded family of analytic amplitudes. The
supplier yields

$$
\int_{-\beta}^{\beta}e^{-n\tau^2/2}q(\tau)\,d\tau
=\sqrt{\frac{2\pi}{n}}q(0)+O(K_q n^{-3/2}).
$$

The general remainder theorem is not proved again or applied
verbatim to the varying $h_{n,y}$. The work here is an application
to the actual source and a joint same-node sign, not a claim of
literature originality. It has no new Lean certification.

### The source bounds required by the contour

On every fixed compact subset
$D$ of the open lower half-plane, choose the principal square root
and put $s_n(u)=1/2+i\omega_n\sqrt u$. Then
$\Re s_n(u)\ge c_D\omega_n$. The Dirichlet series gives
$\zeta(s_n(u))=1+O_D(2^{-c_D\omega_n})$, after decreasing the
positive constant if needed. There is consequently a holomorphic
logarithm of $F(r_nu)$ on a neighborhood of $D$, obtained from

$$
\log F(r_nu)=
\log\frac1{2\xi_0}+\operatorname{Log}s_n(u)
+\operatorname{Log}(s_n(u)-1)
+\log\Gamma(s_n(u)/2)-\frac{s_n(u)}2\log\pi
+\log\zeta(s_n(u)).
$$

Here the logarithm of Gamma is the analytic branch on the right
half-plane, and the last logarithm is its branch near one. Stirling
in its stated sector gives

$$
L_n(u):=\frac1n\log F(r_nu)\longrightarrow2i\sqrt u
$$

locally uniformly there. The same convergence holds for every fixed
number of analytic derivatives on smaller compact sets, by Cauchy
estimates on a fixed larger neighborhood. No logarithm is asserted
on the whole circle or at source zeros.

For the whole circle, reuse the complete original positive even
kernel and all-complex Fourier representation already identified
in this note. For real $v,w$, the triangle inequality and evenness
supply the exact estimate

$$
|\Xi(v+iw)|\le\int_{\mathbb R}\Phi(x)e^{-wx}\,dx
=\xi(1/2+|w|).
$$

Consequently, for $u=\rho e^{i\theta}$, $-\pi\le\theta\le\pi$,

$$
|F(r_n\rho e^{i\theta})|
\le F\bigl(-r_n\rho\sin^2(\theta/2)\bigr)
=\frac{\xi(1/2+\omega_n\sqrt\rho\,|\sin(\theta/2)|)}{\xi_0}. \tag{LC50}
$$

At the positive-axis crossing the bound is exactly one; no
logarithm or nonvanishing assertion is needed there. Along the
positive real argument, the Gamma formula and Stirling give

$$
\log\frac{\xi(1/2+x)}{\xi_0}
=\frac x2\log\frac{x}{2\pi}-\frac x2+O(\log(2+x)),
\qquad x\ge0,
$$

where $x\log x$ is continuously extended at zero. The compact
range is absorbed into the error using positivity and continuity
of the original kernel transform. Set
$x=\omega_n\sqrt\rho\,q$, $q=|\sin(\theta/2)|$.
On each fixed positive compact interval of $\rho$, the function
$\sqrt\rho\,q\log(\sqrt\rho\,q)$ is uniformly bounded including
$q=0$. Thus the exact theta bound yields

$$
\log|F(r_n\rho e^{i\theta})|
\le \frac{\omega_n\log\omega_n}{2}
       \sqrt\rho\,|\sin(\theta/2)|+O(\omega_n+\log\omega_n),
$$

uniformly on this annulus, with $\log0=-\infty$ at source zeros.
In particular,

$$
\frac1n\log|F(r_n\rho e^{i\theta})|
\le2\sqrt\rho\,|\sin(\theta/2)|+o(1).
$$

This uses the full original kernel rather than an approximating
measure. It pays the whole-circle upper envelope without a
horizontal zero-strip hypothesis, a zeta lower bound on the
critical line, or an RH premise.

### Finite saddles and one common complex amplitude

Fix $Y=[a,b]\subset(1/4,\infty)$. The exact Cauchy coefficient
formula for every fixed $d\in\{-1,0,1\}$ is

$$
A_{n+d,f_n}(y)
=\frac{(n+d)!}{n^{n+d}} I_{n,d}(y),\qquad
I_{n,d}(y)=\frac1{2\pi i}
 \oint e^{nyu}F(r_nu)u^{-n-d-1}\,du,
\qquad y\in Y. \tag{LC51}
$$

Define only on the lower local neighborhood

$$
h_{n,y}(u)=yu+L_n(u)-\operatorname{Log}u,
\qquad h_y(u)=yu+2i\sqrt u-\operatorname{Log}u.
$$

The limiting lower saddle is

$$
\sqrt{u_*(y)}=\frac{\sqrt{4y-1}-i}{2y},\qquad
|u_*(y)|=\frac1y,
$$

and its angular Gaussian coefficient is

$$
a_*(y)=u_*(y)^2h_y''(u_*(y))
=1-\frac{i\sqrt{u_*(y)}}2,
\qquad \Re a_*(y)=1-\frac1{4y}>0. \tag{LC52}
$$

The source's local analytic derivative convergence and this simple
saddle give a lower finite saddle $u_n(y)$ of $h_{n,y}$, uniformly
for $y\in Y$, with $u_n(y)\to u_*(y)$. Set

$$
\rho_n(y)=|u_n(y)|,
\qquad a_n(y)=u_n(y)^2h_{n,y}''(u_n(y)).
$$

Use the circle $|u|=\rho_n(y)$ in the exact contour. It passes
through both the finite saddle and its conjugate; no approximate
node or leading-phase saddle is substituted into the integrand.
Its angular second derivative at the lower saddle is $-a_n(y)$,
and $\Re a_n(y)$ has a uniform positive lower bound.

To check dominance, the limiting real envelope on $|u|=1/y$ is

$$
H_y(\theta)=\cos\theta+\frac2{\sqrt y}|\sin(\theta/2)|+\log y.
$$

Writing $q=|\sin(\theta/2)|$ gives
$H_y=1-2q^2+2q/\sqrt y+\log y$. Its only maxima are the two
conjugate angles of $u_*(y)$, where $q=1/(2\sqrt y)$.
Since $Y$ is compact and excludes $1/4$ and infinity, these angles
are uniformly separated from each other and from $0,\pm\pi$.
Outside fixed small neighborhoods the envelope has a uniform
positive gap. The full-circle upper bound, $\rho_n\to1/y$, and
the exact local phase convergence transfer that gap to the finite
contour relative to $\Re h_{n,y}(u_n(y))$.
Inside either neighborhood, the local analytic derivatives are
uniformly bounded and the real quadratic decay has a uniform
positive coefficient. To apply the fixed-phase supplier, write

$$
\phi_{n,y}(v)=h_{n,y}(u_n(y)e^{iv}),\qquad
\tau=v\sqrt{\frac{2(\phi_{n,y}(0)-\phi_{n,y}(v))}{v^2}}. \tag{LC53}
$$

The quotient extends analytically to $a_n(y)$ at zero. Choose
the square root with positive real part; then
$\tau'(0)=\sqrt{a_n(y)}$ and exactly
$\phi_{n,y}(v)=\phi_{n,y}(0)-\tau^2/2$.
Uniform nondegeneracy and analytic derivative bounds give an
inverse $v=\chi_{n,y}(\tau)$ on one fixed disk, with uniform
bounds. The image of the local real $v$ arc enters and leaves
through opposite Gaussian descent sectors, uniformly separated
from their boundaries, since $\Re a_n$ has a positive lower bound
and $a_n$ has a finite upper bound. Choose a fixed $\beta>0$ inside
this disk and smaller than the endpoint radii. Holomorphy permits
replacement by $[-\beta,\beta]$ and connecting paths in these sectors.
The connecting paths can stay at radius at least $\beta$ and have
$\Re(\tau^2)\ge c\beta^2$ for a uniform $c>0$, so their errors are
uniformly exponentially small.

Since $du/(iu)=dv$, the transformed amplitude is

$$
q_{n,d,y}(\tau)
=\bigl(u_n(y)e^{i\chi_{n,y}(\tau)}\bigr)^{-d}
     \chi_{n,y}'(\tau),\qquad
q_{n,d,y}(0)=\frac{u_n(y)^{-d}}{\sqrt{a_n(y)}}.
$$

It is uniformly bounded on the fixed analytic disk and contour
for $y\in Y$ and $d=-1,0,1$. These are the fixed phase, contour,
neighborhood and uniform $K_q$ conditions needed to reuse
Corollary 5.1. The varying exact phase has been absorbed into the
amplitude by an analytic coordinate, not discarded from the
exponent.

Choose the square root of $a_n$ with positive real part and define

$$
B_n(y)=\frac{\exp(nh_{n,y}(u_n(y)))}{\sqrt{2\pi n a_n(y)}}\ne0. \tag{LC54}
$$

The fixed-phase supplier with the verified uniform conditions gives

$$
I_{n,d}(y)=2\Re\bigl(B_n(y)u_n(y)^{-d}\bigr)
               +O_Y(|B_n(y)|/n),\qquad d=-1,0,1, \tag{LC55}
$$

uniformly for $y\in Y$, with the same $B_n,u_n$ for all three
offsets. The upper contribution is the conjugate of the lower one.
Neither $h_{n,y}$ nor its exponential is replaced by its limit;
a normalized $o(1)$ phase error can still have an unbounded
$n$-multiple.

### The actual-node product on each compact bulk interval

At any actual positive $\mathcal J_n(t)$ zero with
$y=r_n/t\in Y$, (LC46) gives $I_{n,0}(y)=0$, hence
$\Re B_n(y)=O_Y(|B_n(y)|/n)$. For every complex $B\ne0,u\ne0$,

$$
4\Re(Bu)\Re(B/u)
=-4|B|^2\frac{(\Im u)^2}{|u|^2}+4(\Re B)^2.
$$

Applying this identity and the simultaneous absolute errors yields,
uniformly over these actual nodes,

$$
\frac{I_{n,-1}(y)I_{n,1}(y)}{|B_n(y)|^2}
=-4\frac{(\Im u_n(y))^2}{|u_n(y)|^2}+O_Y(1/n)
\longrightarrow-\frac{4y-1}{y^2}<0. \tag{LC56}
$$

The right side is uniformly bounded away from zero on $Y$.
Consequently, for some finite $N_Y$ and all $n\ge N_Y$, every
actual positive node with $t/r_n\in[1/b,1/a]\subset(0,4)$ satisfies

$$
A_{n-1,f_n}(y)A_{n+1,f_n}(y)<0,
\qquad \mathcal J_n'(t)\mathcal G_n(t)>0. \tag{LC57}
$$

The second assertion is exactly (LC47). The first also makes both
adjacent Appell values nonzero, so these nodes are simple and have
no indicated adjacent collision. It assumes neither complete
row positivity nor an unbounded positive-root subsequence.
It asserts a sign only for actual positive nodes in the displayed
compact bulk interval, without asserting that such nodes exist.

No numerical value of $N_Y$ is supplied. The argument excludes both
$y\downarrow1/4$ and $y\to\infty$, thus the $t/r_n=4$ edge and
the $t/r_n\to0$ regime, as well as nodes beyond the upper edge.
In particular fixed source-height clusters lie outside this
compact bulk statement. A compact-bulk sign, even without RH
as a premise, does not pay the original all-node sign or its
low-degree and edge collision duties. RH and strict Robin for
every integer greater than 5040 remain unresolved.

## Excluding all positive outer nodes by one negative saddle

Reuse the original source, (LC31), (LC46), the exact angular bound
(LC50), and the fixed-Gaussian Perron application used for (LC55).
The following source-specific application concerns all actual
positive real nodes, without complete-row positivity or RH as a
premise. It does not derive a finite-root edge from the conditional
weak law (LC44), and it has no new Lean certification or claim of
literature originality.

Fix $0<a<1/4$, and now take $Y=[0,a]$. The limiting saddle radius is

$$
r(y)=\frac{2}{1+\sqrt{1-4y}},\qquad
u_*(y)=-r(y)^2,\qquad 1\le r(y)\le r(a)<2. \tag{LC58}
$$

This includes $y=0$ with $r(0)=1$. The identity
$yr(y)^2-r(y)+1=0$ selects the smaller negative saddle; for $y>0$
the other root is not used as the circle radius.

### The local phase across the negative axis

On a fixed complex neighborhood of the compact negative segment
$\{u_*(y):y\in Y\}$, choose $\sqrt{-u}$ positive on the negative
axis, and set

$$
s_n(u)=1/2+\omega_n\sqrt{-u},\qquad
F(r_nu)=\frac{\xi(s_n(u))}{\xi_0}.
$$

The second equality uses the same even square-variable source and
xi reflection, rather than replacing it by another function.
This neighborhood can be chosen with $\Re\sqrt{-u}\ge c>0$.
The source is therefore nonzero for all sufficiently large $n$:
$\Re s_n\ge c\omega_n$, the Dirichlet series tends to one, and
Gamma and the polynomial factors are nonzero there. The same
analytic Gamma–zeta logarithm as before defines $\ell_n(u)$,
real on the negative segment and satisfying

$$
e^{\ell_n(u)}=F(r_nu),\qquad
\ell_n(u)/n\longrightarrow2\sqrt{-u}. \tag{LC59}
$$

locally uniformly with every fixed number of derivatives. This
uses the already established coefficient scale and sectorial
Stirling argument, now on a neighborhood crossing the negative
axis. It asserts no global source logarithm.

Choose the local branch $\operatorname{Log}u=
\operatorname{Log}(-u)+i\pi$, and define the exact and limiting
local phases

$$
h_{n,y}(u)=yu+\ell_n(u)/n-\operatorname{Log}u,
\qquad
h_y(u)=yu+2\sqrt{-u}-\operatorname{Log}u.
$$

At $u_*(y)$ the limiting derivative is zero, and its angular
Gaussian coefficient is

$$
u_*(y)^2 h_y''(u_*(y))=1-r(y)/2\ge1-r(a)/2>0.
$$

Uniform local analytic convergence and this nondegeneracy give a
nearby exact saddle $u_n(y)\to u_*(y)$ uniformly on $Y$. Its
uniqueness is only in the selected neighborhood. The local
logarithm is real on the negative axis, apart from the constant
$-i\pi$ in $h_{n,y}$, so conjugation and local uniqueness imply
$u_n(y)$ is real. It is negative for large $n$. Consequently

$$
\rho_n(y)=-u_n(y)>0,\qquad
q_n(y)=u_n(y)^2h_{n,y}''(u_n(y))>0,
\qquad \inf_{y\in Y}q_n(y)>c_a>0. \tag{LC60}
$$

All relevant derivative bounds and radii are uniform including
$y=0$; none divides by $y$.

### One actual saddle is the unique dominant point

Use $|u|=\rho_n(y)$ in the exact coefficient integral (LC51),
with $d=0$. The negative real point is counted once, by the angular
parameter $u=u_n(y)e^{iv}$, $-\pi\le v\le\pi$. At the limiting
radius $\rho=r(y)^2$, (LC50) gives the real envelope

$$
E_y(\theta)=yr(y)^2(1-2q^2)+2r(y)q-2\log r(y),
\qquad q=|\sin(\theta/2)|\in[0,1].
$$

Its derivative as a function of $q$ satisfies

$$
\partial_qE_y=2r(y)-4yr(y)^2q
\ge2r(y)-4yr(y)^2=4-2r(y)\ge4-2r(a)>0.
$$

Thus the negative point, where $q=1$, is the unique circle maximum.
The angles $\theta=\pi,-\pi$ label the same point and are not two
saddle contributions. Outside a fixed neighborhood of that point
the envelope has a uniform positive gap, for all $y\in[0,a]$.
The annular estimate following (LC50) is uniform also at the
auxiliary envelope endpoint $q=0$: its compact $x$ range was
absorbed using positivity and continuity, before rescaling. No
large-argument Stirling estimate is used at that endpoint.
The exact radius convergence and local phase convergence transfer
this gap to the finite contour relative to
$\Re h_{n,y}(u_n(y))$. Near the point, the real quadratic decay
has the uniform coefficient $q_n>0$.

The exact local Gaussian coordinate (LC53), with coefficient
$q_n$ in place of $a_n$, has a common analytic inverse disk and
uniform bounded amplitude. Reuse the same fixed-phase
Corollary 5.1 after this change of coordinate; the outer contour
and short descent-sector connectors are uniformly exponentially
small. There is now one saddle, with no real-part cancellation.
Its nonzero leading contribution is real and has known sign:

$$
D_n(y)=
\frac{e^{nyu_n(y)}F(r_nu_n(y))u_n(y)^{-n}}
     {\sqrt{2\pi n q_n(y)}},
\qquad (-1)^nD_n(y)>0. \tag{LC61}
$$

The actual source is positive on the negative axis by the original
kernel representation, and the square root is positive real.
The resulting remainder is relative to this exact finite
amplitude, not its limiting approximation:

$$
\frac{n^n}{n!}A_{n,f_n}(y)
=D_n(y)+O_a(|D_n(y)|/n),\qquad 0\le y\le a, \tag{LC62}
$$

uniformly in $y$. In particular there is $N_a$ such that

$$
(-1)^nA_{n,f_n}(y)>0
\qquad(n\ge N_a,\ 0\le y\le a). \tag{LC63}
$$

At $y=0$ this agrees with the exact finite coefficient
$A_{n,f_n}(0)=(-1)^n n!a_n(r_n/n)^n$; it requires no extension
of the variable substitution $y=r_n/t$ to an infinite node.

### The actual-positive-root upper bound and what it leaves

For an actual positive $\mathcal J_n(t)$ root, its finite
$y=r_n/t>0$ makes $A_{n,f_n}(y)=0$ by (LC46). The uniform
zero-free result forces $y>a$, so $t<r_n/a$. Taking
$a=1/(4+\varepsilon)$ gives the exact quantifiers

$$
\forall\varepsilon>0\ \exists N_\varepsilon\
\forall n\ge N_\varepsilon\ \forall t>0:
\quad \mathcal J_n(t)=0\ \Longrightarrow\
t<(4+\varepsilon)r_n. \tag{LC64}
$$

This excludes every actual positive real outlier beyond each
fixed upper-edge neighborhood. It assumes neither existence of
positive nodes nor that all other roots are real; no conclusion
about complex outliers follows. No numerical $N_\varepsilon$
or uniformity as $\varepsilon\downarrow0$ is supplied. The
limiting collision at $y=1/4$ remains outside this single-saddle
range; the finite fold is retained separately below. Together with
(LC57), the remaining full-criterion obligations include the
shrinking soft-edge neighborhood,
$t/r_n\to0$ through heights growing with degree, plus
initial degrees, complex-root control and common-zero/multiplicity
propagation outside the established ranges. The fixed real height bands already have
the source-dependent eventual sign in (LC30); the missing step
is uniform control across a growing band. The bound does not assert
complete hyperbolicity or prove RH or strict Robin for every $H>5040$.

## The finite soft-edge fold and its first displacement

Reuse the actual source and (LC31), the local analytic Gamma–zeta
logarithm across the negative axis established before (LC59), and
sectorial Stirling. This source-specific parameter application does
not claim literature originality or Lean certification. It does
not assume RH or complete-row hyperbolicity. Its fold is a critical
point of the exact phase, not an actual polynomial root.

Put $w_n=W(2n/\pi)$ and $\omega_n=\sqrt{r_n}$ as before. On a fixed
complex disk about $\rho=4$, sufficiently small to have positive real
part, take $\sqrt\rho>0$ on the positive axis and define

$$
\mathcal L_n(\rho)=\frac1n\log F(-r_n\rho),\qquad
H_{n,y}(\rho)=-y\rho+\mathcal L_n(\rho)-\operatorname{Log}\rho.
$$

The source logarithm is analytic and real on the positive segment;
its nonvanishing comes from the right-half-plane Gamma–zeta formula.
The same sectorial expansion gives, uniformly on a slightly larger
fixed disk lying in the same right-half-plane branch,

$$
\mathcal L_n(\rho)=\frac{\omega_n\sqrt\rho}{2n}
\left(\operatorname{Log}\frac{\omega_n\sqrt\rho}{2\pi}-1\right)
+O\left(\frac{\log n}{n}\right). \tag{LC65}
$$

The defining Lambert identity is $w_ne^{w_n}=2n/\pi$. Hence (LC31)
implies

$$
\frac{\omega_n}{2n}=\frac2{w_n}
\left(1+O\left(\frac{\log n}{n}\right)\right),\qquad
\log\frac{\omega_n}{2\pi}=w_n+O\left(\frac{\log n}{n}\right).
$$

Substitution into the published source estimate yields

$$
\mathcal L_n(\rho)=2\sqrt\rho+
\frac{\sqrt\rho(\operatorname{Log}\rho-2)}{w_n}
+O\left(\frac{\log n}{n}\right). \tag{LC66}
$$

Cauchy estimates on the larger disk give the same uniform order
for every fixed number of derivatives on a smaller disk. This is
an expansion of the normalized logarithm; the remainder cannot
be discarded after multiplication by $n$ in the exponent.
In particular,

$$
\begin{aligned}
\mathcal L_n'(\rho)&=\rho^{-1/2}
 +\frac{\operatorname{Log}\rho}{2w_n\sqrt\rho}
 +O(\log n/n),\\
\mathcal L_n''(\rho)&=-\frac1{2\rho^{3/2}}
 +\frac{2-\operatorname{Log}\rho}{4w_n\rho^{3/2}}
 +O(\log n/n).
\end{aligned} \tag{LC67}
$$

Let $g_n(\rho)=\mathcal L_n''(\rho)+\rho^{-2}$. Its limit has
$g_*(4)=0$ and $g_*'(4)=-1/128$. Choose one small fixed real
neighborhood of $4$ on which $g_*'<0$. Uniform derivative convergence
makes $g_n$ strictly decreasing there, with opposite endpoint signs,
for sufficiently large $n$. Consequently it has exactly one real
zero there, denoted $\rho_n^{\mathrm e}$. Define

$$
y_n^{\mathrm e}=\mathcal L_n'(\rho_n^{\mathrm e})-
\frac1{\rho_n^{\mathrm e}}. \tag{LC68}
$$

These exact finite parameters satisfy
$\partial_\rho H_{n,y_n^{\mathrm e}}(\rho_n^{\mathrm e})=
\partial_\rho^2 H_{n,y_n^{\mathrm e}}(\rho_n^{\mathrm e})=0$.
Moreover,

$$
\partial_\rho^3H_{n,y_n^{\mathrm e}}(\rho_n^{\mathrm e})
=-\frac1{128}+O(1/w_n),\qquad
\partial_y\partial_\rho H_{n,y}=-1. \tag{LC69}
$$

Thus the cubic degeneracy and its parameter unfolding are nonzero;
no assertion is made that these are the only critical points globally.
At $4$ the correction is

$$
g_n(4)=\frac{1-\log2}{16w_n}+O(\log n/n).
$$

First the fixed derivative bound implies
$\rho_n^{\mathrm e}-4=O(1/w_n+\log n/n)$.
Taylor expansion then gives

$$
\rho_n^{\mathrm e}=4+\frac{8(1-\log2)}{w_n}
 +O(w_n^{-2}+\log n/n), \tag{LC70}
$$

$$
y_n^{\mathrm e}=\frac14+\frac{\log2}{2w_n}
 +O(w_n^{-2}+\log n/n). \tag{LC71}
$$

The first-order change of
$\rho^{-1/2}-\rho^{-1}$ vanishes at $\rho=4$, so the displayed
$y$ correction comes from the explicit $w_n^{-1}$ term, not from
a first-order displacement of $\rho$. Equivalently, the inverse
phase coordinate is

$$
\frac1{y_n^{\mathrm e}}=4-\frac{8\log2}{w_n}
 +O(w_n^{-2}+\log n/n). \tag{LC72}
$$

It is not asserted to be the height of any actual Jensen root.
Since $w_n\sim\log n$,

$$
n^{2/3}\left(y_n^{\mathrm e}-\frac14\right)
\longrightarrow+\infty. \tag{LC73}
$$

The exact finite cubic scale is therefore not centered at the
limiting $1/4$. The displayed remainder bound for this first
corrected approximation is larger than $n^{-2/3}$ and is therefore insufficient to replace
the exact $y_n^{\mathrm e}$ in a bounded Airy argument. This is a
limitation of the bound, not a lower bound on the actual error.
A transition estimate must retain the exact finite fold or prove a stronger remainder.

### A Lambert reference center accurate on the cubic scale

The preceding normalized source expansion has more information than
its first-order fold displacement: the entire displayed function of
$\rho$ approximates the exact logarithm with derivative errors
$O(\log n/n)$. Define its analytic reference

$$
\Lambda_n(\rho)=2\sqrt\rho+
\frac{\sqrt\rho(\operatorname{Log}\rho-2)}{w_n}. \tag{LC74}
$$

Let $v_n=W(4n/(\pi e))$, using the positive real Lambert branch,
and put

$$
\widehat\rho_n=\frac{4w_n^2}{v_n^2},\qquad
\widehat y_n=\frac{v_n(v_n+2)}{4w_n^2}. \tag{LC75}
$$

They tend to $4$ and $1/4$. These are exact reference parameters,
not a new source or actual Jensen roots. Indeed, with
$r=\sqrt\rho$, the reference fold equation
$\Lambda_n''(\rho)+\rho^{-2}=0$ is exactly

$$
r(w_n+\log r-1)=2w_n.
$$

Putting $v=w_n+\log r-1$ gives
$ve^v=2w_ne^{w_n-1}=4n/(\pi e)$. Reuse the defining Lambert
inverse, [DLMF (4.13.1) and its principal real branch](https://dlmf.nist.gov/4.13),
to obtain $v=v_n$, $r=2w_n/v_n$, and thus
$\rho=\widehat\rho_n$. Direct substitution gives
$\Lambda_n'(\widehat\rho_n)-\widehat\rho_n^{-1}
=\widehat y_n$.

On the same fixed neighborhood the difference between
$g_n=\mathcal L_n''+\rho^{-2}$ and
$\widehat g_n=\Lambda_n''+\rho^{-2}$ is $O(\log n/n)$,
and, for all sufficiently large $n$, both centers lie in the same
fixed real interval $I$ on which $g_n'(\rho)\le-c<0$, with $c$
independent of $n$. Since
$\widehat g_n(\widehat\rho_n)=0$, the mean value estimate at the
unique exact local zero gives

$$
\rho_n^{\mathrm e}-\widehat\rho_n=O(\log n/n). \tag{LC76}
$$

The first derivative source error and Taylor expansion of
$\Lambda_n'(\rho)-\rho^{-1}$ then give

$$
y_n^{\mathrm e}-\widehat y_n=O(\log n/n),\qquad
n^{2/3}|y_n^{\mathrm e}-\widehat y_n|\longrightarrow0. \tag{LC77}
$$

Thus this closed reference locates the exact fold more accurately
than a cubic-scale window, unlike a truncation at the displayed
$w_n^{-1}$ shift. This controls a center coordinate only. It does
not permit replacing the exact source phase or common amplitude:
$n(\mathcal L_n-\Lambda_n)=O(\log n)$ need not vanish. The
Airy contour, uniform remainder and actual-node sign remain unpaid.

This computes a phase parameter and its displacement only. It
supplies no uniform Airy remainder, adjacent-row sign, real-root
existence, complex-root exclusion, starting degree or RH/Robin
conclusion. Those obligations retain their original quantifiers.
