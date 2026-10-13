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

The [second-level concavity source](../Zeros/planatsole2026secondlevel.md)
states a finite-order inequality for $K(\sqrt T)$ in Csordas'
normalization $\Phi(x)=2K(x/2)$, so its receiving coordinate is
$T=x^2/4$. The [original-variable derivative counterexample](../Zeros/sra2026thetakernelcounterexample.md)
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
[the existing Jensen supplier](../Zeros/osullivan2021modifiedjensen.md) and
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
[Zacharovas, Theorem 2.8](../Asymptotics/zacharovas2025depoissonization.md)
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
range; the finite fold is retained separately below. The fixed and
logarithmic soft-edge window estimates alone do not overlap (LC57);
(LC107)–(LC133) supply the common-domain fixed-band bridge. The remaining
full-criterion obligations include $t/r_n\to0$ through heights growing
with degree, initial degrees, complex-root control and common-zero/
multiplicity propagation outside the established ranges. The fixed real height bands already have
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
$n(\mathcal L_n-\Lambda_n)=O(\log n)$ need not vanish. The following bounded-window application supplies the Airy contour,
uniform errors and actual-node sign only for fixed finite Airy arguments.

The parameter calculation alone supplies no uniform Airy remainder,
adjacent-row sign, real-root existence, complex-root exclusion,
starting degree or RH/Robin conclusion.

## Actual-node signs in bounded finite soft-edge windows

Reuse (LC46)–(LC50), the original-source local
analytic estimates, and the exact finite fold in (LC65)–(LC77).
It reuses the classical Airy contour and derivative representations;
the canonical integral also follows from [Olde Daalhuis–Temme,
(3.1)–(3.4)](https://doi.org/10.1137/S0036141090187685), with constant and linear amplitudes. Their generic
uniform expansion theorem is not proved again, and no global cubic
coordinate for this source is assumed. This source-specific bounded
window application has no Lean or originality certification.

Write $\rho_n=\rho_n^{\mathrm e}$, $y_n=y_n^{\mathrm e}$ and use
$H_{n,y}$ from the finite-fold section. Set

$$
\mathfrak a_n=-\rho_n^3\partial_\rho^3H_{n,y_n}(\rho_n)>0,
\qquad \gamma_n=(2/\mathfrak a_n)^{1/3},
\qquad x_n(y)=-\rho_n\gamma_n n^{2/3}(y-y_n). \tag{LC78}
$$

Then $\mathfrak a_n\to1/2$ and $\gamma_n\to4^{1/3}$; these are exact finite
parameters. Fix $0<M<\infty$ and restrict to real $|x_n(y)|\le M$.
Thus $\delta=y-y_n=O_M(n^{-2/3})$ and $y>0$ for large $n$.
Define $c_{n,y}=\exp(nH_{n,y}(\rho_n))>0$ and, locally,

$$
P_{n,y}(\theta)=H_{n,y}(\rho_ne^{i\theta})-H_{n,y}(\rho_n).
$$

The source logarithm is used only in one fixed complex disk around
$\theta=0$. On the whole circle define the common integrand by

$$
Q_{n,y}(\theta)=
\exp[-ny\rho_n(e^{i\theta}-1)-in\theta]
\frac{F(-r_n\rho_ne^{i\theta})}{F(-r_n\rho_n)}. \tag{LC79}
$$

The denominator is positive. This agrees with $e^{nP_{n,y}}$
locally and makes no global source logarithm assumption.
The coefficient contour gives,
simultaneously for $d=-1,0,1$,

$$
I_{n,d}(y)=(-1)^{n+d}c_{n,y}\rho_n^{-d}J_{n,d}(y),
\qquad
J_{n,d}(y)=\frac1{2\pi}\int_{-\pi}^{\pi}
 Q_{n,y}(\theta)e^{-id\theta}\,d\theta. \tag{LC80}
$$

On the entire bounded window, subtract the whole common integral:

$$
J_{n,d}(y)-J_{n,0}(y)=\frac1{2\pi}\int_{-\pi}^{\pi}
 Q_{n,y}(\theta)(e^{-id\theta}-1)\,d\theta,
\qquad d=-1,1. \tag{LC81}
$$

At an actual $I_{n,0}(y)=0$, the normalization gives exactly
$J_{n,0}=0$. No approximate node or Airy zero replaces that condition.

### The original arc has the Airy contour orientation

The source derivatives give, at $\delta=0$,

$$
P'(0)=P''(0)=0,\qquad P'''(0)=i\mathfrak a_n,\qquad
P''''(0)\longrightarrow-3/4.
$$

The fourth derivative is real. Uniform analyticity gives

$$
P_{n,y}(\theta)=-i\rho_n\delta\theta+
 \frac{i\mathfrak a_n}6\theta^3+\mathfrak b_n\theta^4+
 O(|\theta|^5+|\delta||\theta|^2),
\qquad \mathfrak b_n=P_{n,y_n}''''(0)/24\longrightarrow-1/32. \tag{LC82}
$$

Choose a small fixed $\eta>0$ inside this disk. The normalized full
theta bound (LC50), at $\rho_n\to4,y\to1/4$, has limiting real
envelope $-2(1-\cos(\theta/2))^2$. Outside $(-\eta,\eta)$ this
has a fixed negative upper bound. The annular source estimate
includes its auxiliary zero endpoint; hence the normalized original
exterior integral is $O_M(e^{-cn})$.

Deform the short interval to the two rays of arguments $5\pi/6$
and $\pi/6$, directed toward and away from zero, of radius $\eta$.
Join their endpoints to $-\eta$ and $\eta$ on circular arcs
inside the same analytic disk. For the right connector,
$0\le\phi\le\pi/6$,

$$
\Re\frac{i\mathfrak a_n}6\eta^3e^{3i\phi}
=-\frac{\mathfrak a_n}6\eta^3\sin3\phi.
$$

At $\delta=0$, on $0\le\phi\le\pi/12$ the quartic has
$\cos4\phi\ge1/2$ and the cubic is nonpositive; on
$\pi/12\le\phi\le\pi/6$ the cubic has
$\sin3\phi\ge\sin(\pi/4)>0$ and dominates the bounded quartic.
The fifth-order remainder is absorbed by fixing $\eta$ small.
The exact perturbation is $-\rho_n\delta(e^{i\theta}-1)$;
on these fixed arcs its modulus is at most $C_Mn^{-2/3}\eta$.
Increasing $N_M$ makes it smaller than half the fixed negative
quartic bound. The real source branch gives
$P(-\overline\theta)=\overline{P(\theta)}$, so the left connector
has the same estimate. Thus both connectors have
$\Re P\le-c\eta^4$ uniformly for large $n$ in the window. Holomorphy permits this
deformation; connector errors are exponentially small.
The main integral runs into zero on the upper-left Airy ray and
out on the upper-right ray. Under $s=-it$ it is the standard Airy
contour, accounting for variable and contour reversal together.
There is one Airy cycle and no factor two.

### Source-specific absolute errors after scaling

On these rays set $\theta=\gamma_n n^{-1/3}t$. The exact finite
cubic coefficient gives

$$
nP_{n,y}(\theta)=i(t^3/3+x_n(y)t)+R_{n,y}(t),
\qquad
|R_{n,y}(t)|\le C_Mn^{-1/3}(|t|^4+|t|^2). \tag{LC83}
$$

The rays end at $|t|=\eta n^{1/3}/\gamma_n$.
Their canonical cubic has real part $-|t|^3/3$, and the bounded
linear argument contributes at most $M|t|$. Choose $\eta$ small,
then $n$ large, so

$$
\max(\Re R_{n,y}(t),0)\le |t|^3/6+C_M.
$$

Indeed $n^{-1/3}|t|^4\le C\eta|t|^3$ on the truncated rays,
and the quadratic term is absorbed into a small cubic multiple
plus a constant. Bound
$|e^R-1|\le |R|e^{\max(\Re R,0)}$ and use the finite moments
of $e^{-|t|^3/6+M|t|}$: the scaled integral error is
$O_M(n^{-1/3})$. Extending the canonical rays to infinity costs
an exponentially small error. Reusing [DLMF (9.5.4)](https://dlmf.nist.gov/9.5.E4), whose
constant and linear amplitude forms also appear in
Olde Daalhuis–Temme (3.1)–(3.4), yields

$$
J_{n,0}(y)=\gamma_n n^{-1/3}\mathrm{Ai}(x_n(y))
 +O_M(n^{-2/3}). \tag{LC84}
$$

For the canceled neighboring amplitude,

$$
e^{-id\gamma_n n^{-1/3}t}-1
=-id\gamma_n n^{-1/3}t+O(n^{-2/3}|t|^2),
\qquad d=-1,1.
$$

Its Taylor remainder constant is uniform because $|\theta|\le\eta$.
Multiplying the linear term by $e^R-1$ costs another
$O_M(n^{-2/3})$ in the bracket, with the same cubic weight.
The outer factor $\gamma_n n^{-1/3}$ makes both this error
and the amplitude remainder $O_M(n^{-1})$. The classical Airy
derivative representation therefore gives throughout the window,

$$
J_{n,d}(y)-J_{n,0}(y)=-d\gamma_n^2n^{-2/3}\mathrm{Ai}'(x_n(y))
 +O_M(n^{-1}),\qquad d=-1,1. \tag{LC85}
$$

The finite prefactor and the shared constants for all nodes and
three offsets are retained.

### The actual-node product

The middle expansion at these nodes gives
$\mathrm{Ai}(x_n)=O_M(n^{-1/3})$. The classical Airy function
and its derivative have no common zero, by the nonzero
[DLMF (9.2.7) Wronskian](https://dlmf.nist.gov/9.2.E7); their squared sum has
a positive minimum on $[-M,M]$. Thus
$|\mathrm{Ai}'(x_n)|\ge c_M>0$ for sufficiently large $n$
at all the actual nodes under consideration. Consequently,

$$
I_{n,-1}(y)I_{n,1}(y)=
-c_{n,y}^2\gamma_n^4n^{-4/3}\mathrm{Ai}'(x_n(y))^2
+O_M(c_{n,y}^2n^{-5/3})<0. \tag{LC86}
$$

The integer signs multiply to $+1$ and the $\rho_n$ powers cancel.
The positive factorial correspondence and (LC47) then give the
original strictly positive derivative comparison at every actual
positive Jensen node in this bounded finite soft-edge window.
Both adjacent values are nonzero there; existence of nodes is
not asserted or required as a premise.

The exact quantifiers in the original node coordinate are

$$
\forall M>0\ \exists N_M\ \forall n\ge N_M\ \forall t>0:
\quad
\bigl(\mathcal J_n(t)=0,\ |x_n(r_n/t)|\le M\bigr)
\Longrightarrow \mathcal J_n'(t)\mathcal G_n(t)>0. \tag{LC87}
$$

No numerical $N_M$ is supplied.
The following pointwise estimates control an explicit growing Airy
window. These window estimates alone do not supply a uniform overlap
with bulk ranges approaching the fold; (LC107)–(LC133) supply that
fixed-band overlap. The growing hard-edge band, complex roots, initial
degrees and global collision propagation remain unresolved.
RH and strict Robin for all integers greater than 5040 remain unresolved.

## Pointwise errors and an explicit growing soft-edge window

Reuse the exact finite fold and original canceled contour formulas
(LC78)–(LC85). Retain $\varepsilon=n^{-1/3}$ and the exact
$\rho_n,y_n,\gamma_n,x_n,c_{n,y},J_{n,d}$, with the same $f_n$
for $d=-1,0,1$. The classical Airy representations, real-axis
asymptotic envelopes and Wronskian are reused from
[DLMF 9.5](https://dlmf.nist.gov/9.5),
[DLMF 9.7](https://dlmf.nist.gov/9.7) and
[DLMF (9.2.7)](https://dlmf.nist.gov/9.2.E7).
This source-specific application has no Lean or originality certification.

For any fixed $c_0>0$, put $M_n=c_0(\log n)^{2/3}$ and
$|x|=|x_n(y)|\le M_n$. The exact parameter displacement is
$\delta=-x\varepsilon^2/(\rho_n\gamma_n)$, so the original
exterior-circle and connecting-arc gaps persist uniformly on
this parameter set. Increase the starting degree so that
$1\le\gamma_n\le2$ and $3\le\rho_n\le5$.

On the finite upper Airy rays, use $\theta=\gamma_n\varepsilon t$,
$r=|t|\le T_n=\eta/(\gamma_n\varepsilon)$ and
$q_x(t)=i(t^3/3+xt)$. The original source's fixed analytic norms give

$$
nP_{n,y}(\theta)=q_x(t)+R_{n,x}(t),\qquad
|R_{n,x}(t)|\le C_P\varepsilon(r^4+|x|r^2). \tag{LC88}
$$

Choose one fixed $\eta\le1$ with $C_P\eta\le1/12$, and require
$C_P\varepsilon M_n\le1/12$. Then
$|R_{n,x}(t)|\le r^3/6+1/12$. Both rays have
$\operatorname{Im}t=r/2$. Write

$$
U=1+|x|,\qquad v=(-x)_+,\qquad
\zeta=\frac23(x_+)^{3/2}. \tag{LC89}
$$

The direction of the linear term is retained:

$$
e^{\Re q_x(t)+|R_{n,x}(t)|}
\le e^{1/12}\exp(-r^3/6+vr/2). \tag{LC90}
$$

For the finitely many moment orders needed by the two errors, set

$$
W_k(v)=\int_0^\infty r^k e^{-r^3/6+vr/2}\,dr.
$$

The maximum of $-r^3/6+vr/2$ is $v^{3/2}/3$. Split at
$r=2\sqrt{1+v}$; below this point use the maximum, and above it
use $v\le r^2/4$, which leaves an integrable $e^{-r^3/24}$ tail.
Thus

$$
W_k(v)\le K_k(1+v)^{(k+1)/2}e^{v^{3/2}/3},\qquad
K_k=\frac{2^{k+1}}{k+1}
+\frac{24^{(k+1)/3}}3\Gamma\left(\frac{k+1}{3}\right). \tag{LC91}
$$

The middle-row error is bounded by
$C\varepsilon^2(W_4(v)+|x|W_2(v))$. For a neighboring-row
difference, retain the canceled amplitude's linear term and
uniform quadratic remainder; its error is bounded by
$C\varepsilon^3(W_5(v)+|x|W_3(v)+W_2(v))$.
Canonical ray tails and original exterior errors are uniformly
exponentially small, because $T_n\asymp n^{1/3}$ and
$M_n=o(T_n^2)$. Only the canonical rays are extended beyond
the source's fixed analytic disk.

It follows that there are $C_0,C_1>0$ independent of $n,x,d,c_0$
such that, for each fixed $c_0$ and all sufficiently large $n$,

$$
J_{n,0}=\gamma_n\varepsilon\operatorname{Ai}(x)+\mathcal R_0,
\qquad |\mathcal R_0|\le
C_0\varepsilon^2U^{5/2}e^{v^{3/2}/3}, \tag{LC92}
$$

$$
J_{n,d}-J_{n,0}=-d\gamma_n^2\varepsilon^2
\operatorname{Ai}'(x)+\mathcal R_d,
\qquad |\mathcal R_d|\le
C_1\varepsilon^3U^3e^{v^{3/2}/3},\qquad d=-1,1. \tag{LC93}
$$

These track the width dependence from the original phase bounds;
they do not use a growing parameter in an unspecified fixed-$M$ error.

### Weighted derivative floor at the actual node

The cited positive- and negative-axis Airy asymptotics, extended
over a bounded real interval by continuity, give a fixed $B>0$ with

$$
|\operatorname{Bi}(x)|\le B U^{-1/4}e^\zeta,\qquad
|\operatorname{Bi}'(x)|\le B U^{1/4}e^\zeta.
$$

At an actual $I_{n,0}(y)=0$ the exact normalization gives
$J_{n,0}=0$, so $|\operatorname{Ai}(x)|\le
C_0\varepsilon U^{5/2}e^{v^{3/2}/3}$, using $\gamma_n\ge1$.
Define

$$
\Theta_n(x)=\varepsilon U^{11/4}
e^{v^{3/2}/3+\zeta}. \tag{LC94}
$$

If $C_0B\Theta_n(x)\le1/(2\pi)$, the nonzero Wronskian forces
$|\operatorname{Ai}'(x)\operatorname{Bi}(x)|\ge1/(2\pi)$ and hence

$$
|\operatorname{Ai}'(x)|\ge
\frac1{2\pi B}U^{1/4}e^{-\zeta}. \tag{LC95}
$$

The neighboring errors divided by their leading magnitude are at
most $2\pi BC_1\Theta_n(x)$. Once this is at most $1/2$, the real
$J_{n,-1}$ and $J_{n,1}$ have opposite signs. In particular,

$$
I_{n,-1}I_{n,1}=c_{n,y}^2J_{n,-1}J_{n,1}
\le-\frac{c_{n,y}^2\gamma_n^4\varepsilon^4}{16\pi^2B^2}
U^{1/2}e^{-2\zeta}<0. \tag{LC96}
$$

At each real $x$, at most one of $v$ and $x_+$ is nonzero.
Consequently

$$
\sup_{|x|\le M_n}\Theta_n(x)
\le(1+M_n)^{11/4}
n^{-(1-2c_0^{3/2})/3}\longrightarrow0
\qquad\left(0<c_0<2^{-2/3}\right). \tag{LC97}
$$

For example, the explicit choice

$$
M_n=\frac12(\log n)^{2/3}. \tag{LC98}
$$

gives an error ratio of order
$n^{-(1-1/\sqrt2)/3}(\log n)^{11/6}$.
Thus for some $N$ and all $n\ge N$, every actual positive
middle-row node with $|x_n(r_n/t)|\le M_n$ satisfies the original
strict derivative comparison (LC47). No numerical $N$ is supplied.

The classical positive-axis Airy envelope and absence of nonnegative
real Airy zeros, [DLMF 9.9(i)](https://dlmf.nist.gov/9.9#i), give
$\operatorname{Ai}(x)\ge A_0(1+x)^{-1/4}e^{-2x^{3/2}/3}$ for
$x\ge0$ and some $A_0>0$. The middle-row error relative to its
positive leading term is at most $(C_0/A_0)\Theta_n(x)$.
Therefore $J_{n,0}(y)>0$ for $0\le x_n(y)\le M_n$ and large $n$;
this half of the window contains no actual middle-row nodes.

The width in $y$ is $O(n^{-2/3}(\log n)^{2/3})$, which is smaller
than the exact fold's displacement $y_n-1/4\asymp1/\log n$.
For any fixed compact $Y\subset(1/4,\infty)$, this growing Airy
window and $Y$ are eventually disjoint. The fixed-band application
(LC107)–(LC133) supplies the overlap toward the fold that this window
alone does not provide. The growing hard-edge band, complex roots,
initial degrees and global collision propagation remain unresolved. This proves
neither full-row hyperbolicity nor RH or strict Robin for all $H>5040$.

### The linear-coordinate residual is not a uniformly bounded amplitude

The same source derivatives give a concrete distinction between
weighted integral control and an unweighted amplitude norm.
At $x=0$, write $\mathfrak b_n=P^{(4)}(0)/24\to-1/32$.
At the fixed original ray endpoint $\theta=\eta e^{i\pi/6}$,
the scaled residual after extracting the exact cubic is

$$
R_{n,0}\left(\frac{\eta e^{i\pi/6}}{\gamma_n\varepsilon}\right)
=n\mathfrak b_n\eta^4e^{2\pi i/3}+O(n\eta^5). \tag{LC99}
$$

Its real quartic term is $-n\mathfrak b_n\eta^4/2>0$.
By fixing $\eta$ sufficiently small and then $n$ sufficiently large,

$$
\Re R_{n,0}\left(\frac{\eta e^{i\pi/6}}{\gamma_n\varepsilon}\right)
\ge\frac{n\eta^4}{256},\qquad
\left|e^{R_{n,0}}\right|\ge e^{n\eta^4/256}. \tag{LC100}
$$

The complete cubic-weighted kernel still has the preceding
integrable bound. The residual exponential alone has no
$n$-independent supremum on these growing truncated rays.
Applying a full uniform-expansion supplier through a bounded-amplitude
route therefore still requires a different representation, such as
absorbing the higher phase terms into an exact cubic coordinate and
checking its common amplitude domain and growth conditions.

## The positive real outer scale is actually attained

The fixed-window middle-row estimate (LC84) and the unconditional
positive-root enclosure (LC64) together determine the largest
positive real root's leading scale. Reuse the classical negative
real zeros of $\operatorname{Ai}$ from
[DLMF 9.9(i)](https://dlmf.nist.gov/9.9#i) and their simplicity
from the nonzero Wronskian (9.2.7). This is an application of
the existing estimates and the intermediate value theorem,
with no new generic Airy theorem, Lean certificate or originality claim.

Fix any negative real zero $a$ of $\operatorname{Ai}$. Since
$\operatorname{Ai}'(a)\ne0$, choose a fixed interval
$U=[a-\kappa,a+\kappa]$ on which $\operatorname{Ai}'$ is nonzero
and the two endpoint values have opposite signs. Retain the exact
finite parameters and define, for $x\in U$,

$$
Y_n(x)=y_n-\frac{x}{\rho_n\gamma_n}n^{-2/3},\qquad
B_n(x)=\frac{J_{n,0}(Y_n(x))}{\gamma_n n^{-1/3}}. \tag{LC101}
$$

For all sufficiently large $n$, every $Y_n(x)$ here is positive.
By (LC84),

$$
B_n(x)=\operatorname{Ai}(x)+O(n^{-1/3}). \tag{LC102}
$$

uniformly on this fixed interval. The normalized contour is real
and continuous in $x$. Its endpoint signs therefore agree with
the opposite Airy endpoint signs for all sufficiently large $n$.
The intermediate value theorem supplies a real $x_n^*\in U$
with $J_{n,0}(Y_n(x_n^*))=0$. This is an actual coefficient zero,
not an approximate Airy zero. The finite normalization (LC80)
and source correspondence (LC46) give the actual positive root

$$
t_n^*=\frac{r_n}{Y_n(x_n^*)},\qquad \mathcal J_n(t_n^*)=0. \tag{LC103}
$$

At this zero the middle estimate and a fixed lower bound for
$|\operatorname{Ai}'|$ on $U$ give
$|x_n^*-a|=O(n^{-1/3})$. Consequently,

$$
\frac{t_n^*}{r_n}
=\frac{1}{y_n-\dfrac{a}{\rho_n\gamma_n}n^{-2/3}+O(n^{-1})}
\longrightarrow4. \tag{LC104}
$$

One may choose any such actual root for each sufficiently large
degree. The existence and estimate do not assert uniqueness
inside $U$, or that the constructed root is the largest root.

For these degrees the positive-root set is nonempty and finite:
$\mathcal J_n$ is a nonzero degree-$n$ polynomial with constant
term one. Its largest positive real root $t_n^{\max}$ is therefore
well defined. It satisfies $t_n^{\max}\ge t_n^*$, while (LC64)
gives $t_n^{\max}/r_n<4+\epsilon$ for every fixed $\epsilon>0$
and all sufficiently large $n$. The two bounds yield

$$
\lim_{n\to\infty}\frac{t_n^{\max}}{r_n}=4. \tag{LC105}
$$

Together with (LC31), this is equivalently

$$
t_n^{\max}\sim\frac{64n^2}{W(2n/\pi)^2}. \tag{LC106}
$$

It assumes neither RH nor complete-row real-rootedness. It concerns
the largest actual positive real root only; it does not exclude
complex outliers, supply the total real-root count, identify
$t_n^{\max}$ with the constructed Airy root, or prove RH/Robin.
No numerical starting degree or next-order expansion of
$t_n^{\max}$ is supplied.

## Exact cubic rows and the common-domain interface

This application keeps the original square-variable source and the same
$f_n$ for all three offsets. It reuses (LC65)–(LC87), the classical
cubic-coordinate method and the Airy integral and real-axis envelopes.
It does not prove a new generic normal-form or Airy theorem, claim
originality, or provide Lean certification. The fixed-band argument first states its exact common-domain
interface (U); “Supplying the common cubic domain by an existing analytic implicit theorem”
supplies it by applying a published
analytic implicit-function theorem to the actual source family. All new
conclusions concern sufficiently large degrees and actual positive real
Jensen nodes.

### The published local coordinate and its quantifiers

Levinson, *A canonical form for an analytic function of several
variables at a critical point*, Bull. AMS **66** (1960), 68–69,
[DOI 10.1090/S0002-9904-1960-10397-7](https://doi.org/10.1090/S0002-9904-1960-10397-7),
the unnumbered THEOREM on printed p.68, supplies a local analytic
change $w=v+v^2g(z,v)$ reducing an analytic function to an exact
polynomial in $v$. Its assumptions are vanishing $w$ derivatives
of orders $1,\ldots,m-1$ and a nonzero derivative of order $m$ at
the reference point. Its statement and the proof indication on p.69
also cover several analytic parameters. It is a local theorem for
a specified analytic germ; the stated theorem alone does not supply
a common domain and uniform analytic norms for a sequence of germs.

For each fixed sufficiently large $n$, apply its $m=3$ case to
$H_{n,y_e+\delta}(\rho_e+w)$, where
$\rho_e=\rho_n^{\mathrm e}$ and $y_e=y_n^{\mathrm e}$ are the exact
finite fold (LC68). The derivative conditions are exactly (LC69).
Depress the resulting cubic and choose its real cubic scale with
negative source derivative. This gives, locally for that $n$,

$$
H_{n,y}(R_n(s,y))=A_n(y)+s^3/3-\zeta_n(y)s,
\qquad k_n=(-2/h_{3,n})^{1/3}=\rho_e\gamma_n, \tag{LC107}
$$

where $h_{j,n}=\partial_\rho^jH_{n,y_e}(\rho_e)$ and

$$
R_n(0,y_e)=\rho_e,\quad R_{n,s}(0,y_e)=-k_n,\quad
\zeta_n(y_e)=0,\quad \zeta_n'(y_e)=-k_n. \tag{LC108}
$$

The last derivative follows by differentiating
$H_\rho(R_n,y)R_{n,s}=s^2-\zeta_n$ at the fold and using
$H_{\rho y}=-1$. Real-symmetric local branches are chosen throughout.
In particular, $A_n(y_e)=H_{n,y_e}(\rho_e)$ and
$A_n'(y_e)=-\rho_e$. This is a per-$n$ germ construction, not a
verified uniformly bounded coordinate for the full sequence.

**Interface (U).** There must exist $r,\Delta>0$, $C<\infty$ and
$N$ independent of $n$, such that every $n\ge N$ has real-symmetric
jointly analytic $R_n,A_n,\zeta_n$ (in particular real-valued for real
arguments) satisfying (LC107)–(LC108) on
$|s|<4r$, $|y-y_e|<2\Delta$. The image must stay inside the established
source nonvanishing domain. On nested common neighborhoods,
$R_n(\cdot,y)$ must be biholomorphic, its inverse must cover a fixed
source disk about $\rho_e$, the maps and inverses must have uniformly
bounded analytic norms, and $|R_{n,s}|$ must have a uniform positive
lower bound. Uniform analytic convergence in (LC66) supplies source
bounds; invoking the local theorem independently for each $n$ does
not by itself establish these different quantifiers. “Supplying the common cubic domain by an existing analytic implicit theorem”
supplies this common-domain interface through an
existing complex Banach-space analytic implicit-function theorem.

### Exact normalization and the shared adjacent coefficients

The source's upper theta rays map, to first order, by
$s=-i\theta/\gamma_n$. Their image runs from the upper to the lower
right Airy ray, reversing the standard Airy cycle
[DLMF 9.5.4](https://dlmf.nist.gov/9.5#E4). Absorb this common
reversal into the amplitude and normalize the complete original row:

$$
\mathscr G_{n,d}=-R_{n,s}R_n^{-d-1},\qquad
K_{n,d}=(-1)^{n+d}e^{-nA_n(y)}I_{n,d}(y)
=e^{n(H_{n,y}(\rho_e)-A_n(y))}\rho_e^{-d}J_{n,d}(y).
\tag{LC109}
$$

The zero conditions $I_{n,0}=0$, $J_{n,0}=0$ and $K_{n,0}=0$
therefore refer to the same actual node. No approximation is used
in the prefactor. With $q=\sqrt{\zeta_n(y)}$ define

$$
\rho_\pm=R_n(\pm q,y),\qquad h_\pm=-R_{n,s}(\pm q,y)/\rho_\pm,
$$

$$
\alpha_d=\frac{h_+\rho_+^{-d}+h_-\rho_-^{-d}}2,\qquad
\beta_d=\frac{h_+\rho_+^{-d}-h_-\rho_-^{-d}}{2q},\qquad
D_d=\beta_d-\frac{\alpha_d}{\alpha_0}\beta_0. \tag{LC110}
$$

All these quantities have removable limits at $q=0$ and are
independent of the square-root sign. Direct common-row elimination gives

$$
D_d=\frac{h_+h_-}{q(h_++h_-)}
(\rho_+^{-d}-\rho_-^{-d}),\qquad
D_{+1}=-\frac{D_{-1}}{\rho_+\rho_-}. \tag{LC111}
$$

For real parameters in a small source neighborhood, the denominator
$\rho_+\rho_-$ is positive: the saddles are positive real when
$\zeta_n\ge0$, and conjugate when $\zeta_n<0$. At the exact fold,

$$
\alpha_d=k_n\rho_e^{-d-1},\qquad
\beta_d=-R_{n,ss}(0,y_e)\rho_e^{-d-1}
 +(d+1)k_n^2\rho_e^{-d-2},\qquad
D_d=d\rho_e^{-d}\gamma_n^2. \tag{LC112}
$$

The common $R_{n,ss}$ contribution cancels. Thus the opposite
neighboring signs come from one exact source relation, rather than
three separately selected approximations. With these coefficients
the correct elimination is $K_{n,d}-(\alpha_d/\alpha_0)K_{n,0}$,
or its equivalent with $\rho_e^{-d}J_{n,d}$; an unadjusted
$J_{n,d}-(\alpha_d/\alpha_0)J_{n,0}$ has a different coefficient.

Comparing the fourth-order term in (LC107), and then differentiating
in $y$, gives

$$
R_{n,ss}(0,y_e)=-\frac{h_{4,n}k_n^2}{6h_{3,n}},\qquad
R_{n,y}(0,y_e)=-k_nR_{n,ss}(0,y_e)/2,\qquad
A_n''(y_e)=k_nR_{n,ss}(0,y_e). \tag{LC113}
$$

The limiting phase is $-\rho/4+2\sqrt\rho-\log\rho$, so the
already available derivative convergence yields
$h_{3,n}\to-1/128$, $h_{4,n}\to9/1024$, and $k_n^3\to256$.
Consequently

$$
\alpha_0(y_e)\to2^{2/3},\qquad
\beta_0(y_e)\to2^{-2/3}>0,\qquad A_n''(y_e)\to48. \tag{LC114}
$$

For each fixed $n$, Taylor expansion therefore gives

$$
A_n(y_e+\delta)-H_{n,y_e+\delta}(\rho_e)
=\tfrac12k_nR_{n,ss}(0,y_e)\delta^2+O_n(\delta^3). \tag{LC115}
$$

The quadratic coefficient tends to $24$. The exact exponential
in (LC109) cannot be replaced by $1+o(1)$ at fixed nonzero
displacement. Under (U), the Taylor bounds are uniform after
shrinking the common domain, and there exist fixed positive
$a_*,b_*,d_*$ such that on a sufficiently small real fold band

$$
\alpha_0\ge a_*,\quad\beta_0\ge b_*,\quad
D_{-1}\le-d_*,\quad D_{+1}\ge d_*. \tag{LC116}
$$

### The finite-contour remainder

Assume (U) for this subsection and the following fixed-band
consequences. Set $\varepsilon=n^{-1/3}$, $X=n^{2/3}\zeta_n(y)$ and

$$
\mathcal M(X)=(1+|X|)^{-1/4}e^{-2(X_+)^{3/2}/3},\qquad
\mathcal N(X)=(1+|X|)^{1/4}e^{-2(X_+)^{3/2}/3}. \tag{LC117}
$$

Inside the common chart use the standard two-point interpolation
$\mathscr G_{n,d}=\alpha_d+\beta_ds+(s^2-\zeta_n)g_d$.
The interpolation remainder and its derivative are uniformly
bounded by Cauchy integration on a fixed enclosing circle, kept
away from $\pm\sqrt{\zeta_n}$. For a finite local Airy contour
$\Gamma$ the exact integration by parts is

$$
\begin{aligned}
\frac1{2\pi i}\int_\Gamma e^{n\phi_\zeta}\mathscr G_{n,d}\,ds
={}&\alpha_d C_{0,\Gamma}+\beta_d C_{1,\Gamma}
+\frac{[e^{n\phi_\zeta}g_d]_{\partial\Gamma}}{2\pi i n}\\
&-\frac1{2\pi i n}\int_\Gamma e^{n\phi_\zeta}\partial_sg_d\,ds,
\quad \phi_\zeta=s^3/3-\zeta s.
\end{aligned} \tag{LC118}
$$

Only the polynomial canonical integrals $C_{0,\Gamma}$ and
$C_{1,\Gamma}$ are completed with infinite tails. Their complete
values are $\varepsilon\operatorname{Ai}(X)$ and
$-\varepsilon^2\operatorname{Ai}'(X)$. The local $g_d$ need not
have an analytic extension beyond its source disk.

For $\zeta=q^2\ge0$, use truncated paths
$s=q+u e^{\pm i\pi/3}$; exactly
$\Re\phi_\zeta=-2q^3/3-qu^2/2-u^3/3$.
For $\zeta=-q^2\le0$, use the upper exterior path
$s=iq+u(1+i)$ and the interior path
$s=iq-u(1+i)$, $0\le u\le q$, together with their conjugates.
They join at $-q$; their real phases are respectively
$-2qu^2-2u^3/3$ and $-2qu^2+2u^3/3\le-4qu^2/3$.
The resulting truncated absolute integral satisfies
$\int_\Gamma|e^{n\phi_\zeta}|\,|ds|\le C\varepsilon\mathcal M(X)$.
This uses both the cubic scale at $q=0$ and the quadratic scale
$(nq)^{-1/2}$ away from zero. Hence the integral remainder in
(LC118) is at most $C\varepsilon^4\mathcal M(X)$.

### The original contour, fixed-band exterior and finite caps

The contour passage uses the common chart (U) together with an
explicit extension of the original source estimates to the fixed
parameter band. It does not read the bounded-$x$ quantifier in
(LC82) as already covering a fixed band.

Fix once a sufficiently small $\eta>0$, before choosing the
parameter width. Require $\rho_e\eta e^\eta<d/2$, with the common
source coverage radius from (LC133), and choose it smaller if
necessary so the local theta image and the cap paths below stay
inside the common coordinate disk. For the real exterior
$\eta\le|\theta|\le\pi$, the original variable is
$u=-\rho_e e^{i\theta}$: the angle in (LC50) is
$\vartheta=\theta+\pi$ modulo $2\pi$, and hence
$|\sin(\vartheta/2)|=\cos(\theta/2)$. The exact $Q_{n,y}$ of
(LC79) therefore satisfies

$$
\begin{aligned}
\frac1n\log|Q_{n,y}(\theta)|
\le{}&y\rho_e(1-\cos\theta)
+2\sqrt{\rho_e}\cos(\theta/2)
-\mathcal L_n(\rho_e)+o(1)\\
={}&-2(1-\cos(\theta/2))^2
+\delta\rho_e(1-\cos\theta)+o(1),
\qquad \delta=y-y_e.
\end{aligned}
$$

The $o(1)$ is uniform in the angle and independent of $\delta$;
the parameter dependence displayed here is exact. Let
$g_\eta=2(1-\cos(\eta/2))^2>0$ and choose a fixed upper bound
$\rho_e\le\rho^*$. First take $N$ so the uniform $o(1)$ is
at most $g_\eta/4$; then require
$2\rho^*\delta_0\le g_\eta/4$. The real exterior has
$|Q_{n,y}|\le e^{-ng_\eta/2}$ throughout
$|\delta|\le\delta_0$. Its three $J_{n,d}$ integrals have the
same exponential bound because $|e^{-id\theta}|=1$ there.

For the original fixed-radius connecting arcs, write
$P_{n,0}(\theta)=n^{-1}\log Q_{n,y_e}(\theta)$ locally,
with the branch through $P_{n,0}(0)=0$. Reuse the
already established source expansion
$P_{n,0}=i\mathfrak a_n\theta^3/6+\mathfrak b_n\theta^4
+O(\theta^5)$, with $\mathfrak a_n\to1/2$,
$\mathfrak b_n\to-1/32$ and uniform analytic remainder.
On $\theta=\eta e^{i\phi}$, $0\le\phi\le\pi/12$, the cubic
has nonpositive real part and $\cos4\phi\ge1/2$; on
$\pi/12\le\phi\le\pi/6$, the cubic has a negative real part
of fixed order $\eta^3$. Fixing $\eta$ sufficiently small and
then $N$ sufficiently large gives a uniform negative gap
$\Re P_{n,0}\le-b_{\rm arc}<0$ on this arc. For example the
bounds $\mathfrak a_n\ge1/4$, $\mathfrak b_n\le-1/64$
and the uniform remainder give
$b_{\rm arc}=\min\{\eta^4/256,\eta^3/(48\sqrt2)\}$ after
shrinking $\eta$. Real symmetry gives the other arc, with
$5\pi/6\le\phi\le\pi$.
The exact parameter perturbation is
$P_{n,\delta}-P_{n,0}=-\delta\rho_e(e^{i\theta}-1)$.
Require $\delta_0\rho^*\eta e^\eta\le b_{\rm arc}/2$.
Both original connecting arcs then retain half their gap
on the whole fixed band; their offset amplitudes are uniformly
bounded on these finite paths.

These estimates are relative to $e^{nH_{n,y}(\rho_e)}$.
Under (U), (LC115) has a uniform remainder and gives
$|A_n-H_{n,y}(\rho_e)|\le C\delta^2$. Reduce $\delta_0$ so
this is less than one quarter of the smaller original gap.
Equation (LC109) then transports both bounds to the exact
$K_{n,d}$ normalization with a fixed positive exponential gap.

It remains to join the image of the two finite source rays to the
finite canonical contour. The entire theta-ray source curve lies
in $D(\rho_e,d/2)$, where the common inverse $S_n$ is analytic.
Its endpoint expansion, uniformly in $n$, is

$$
S_n(\rho_e e^{i\theta},y)
=-i\theta/\gamma_n+O(|\theta|^2+|\delta|).
$$

With $0<\gamma_*\le\gamma_n\le\gamma^*$, choose
$a_s=\eta/(4\gamma^*)$. Reduce $\eta$ and then $\delta_0$
so both endpoint radii exceed $2a_s$, stay within the common
coordinate disk, and their arguments lie near $\pm\pi/3$.
Choose also $\sqrt{|\zeta_n(y)|}<a_s/10$ uniformly on the band.
Truncate each of the canonical paths described after (LC118)
at its first intersection with $|s|=a_s$.
Their endpoint arguments, and the original image endpoint
arguments, all lie in the fixed right decay sectors
$2\pi/9\le\arg s\le4\pi/9$ and their conjugates.

Join endpoints by radial segments and circle arcs in these
sectors, at radii at least $a_s$. Every such cap remains inside
the common chart. Since $\cos(3\arg s)\le-1/2$ there,
requiring $\zeta_0\le a_s^2/12$ gives

$$
\Re(s^3/3-\zeta_n s)
\le-|s|^3/12\le-a_s^3/12
$$

on every cap. The original ray image and the capped canonical
path have the same endpoints in the simply connected chart
disk, where the exact transformed integrand is holomorphic.
Cauchy's theorem therefore supplies their exact contour
replacement. Taking the canonical contour from the lower to
the upper right endpoint fixes the standard Airy orientation;
the original reverse orientation is already in the minus sign
of $\mathscr G_{n,d}$.

The finite canonical boundary terms have the same cap gap.
Only the degree-zero and degree-one canonical amplitudes are
continued along the displayed cubic paths to infinity. Their
tails start at $|s|=a_s$ and the explicit real phases following
(LC118) bound them by $Ce^{-b_{\rm tail}n}$ for some fixed
$b_{\rm tail}>0$. All local amplitudes and interpolation
remainders remain confined to the common disk.

The original exterior, original connections, canonical caps,
finite boundary terms and polynomial tails now have a combined
fixed gap $b>0$. Finally reduce $\delta_0$ once more to obtain
(LC119). This last reduction keeps every preceding gap while
$\zeta_0\to0$. It makes all these errors uniformly smaller than
$\varepsilon^4\mathcal M(X)$ and completes the original-source
interface used by (LC120).

The comparison with the positive-side Airy decay is precisely

$$
b>\frac23\zeta_0^{3/2},\qquad
\zeta_0=\sup_{n\ge N,\ |y-y_e|\le\delta_0}|\zeta_n(y)|. \tag{LC119}
$$

All errors therefore give the simultaneous original-row estimates

$$
K_{n,d}=\varepsilon\alpha_d\operatorname{Ai}(X)
-\varepsilon^2\beta_d\operatorname{Ai}'(X)+E_{n,d},\qquad
|E_{n,d}|\le C\varepsilon^4\mathcal M(X),\quad d=-1,0,1.
\tag{LC120}
$$

The weaker bound $C\varepsilon^4(\mathcal M+\varepsilon\mathcal N)$
would also suffice below. All constants are independent of the
three offsets and of sufficiently large $n$ on this fixed band.

### Actual-node signs and fixed overlap

At an actual $K_{n,0}=0$ with $X\le0$, the middle estimate is the
exact equality
$\operatorname{Ai}(X)=\varepsilon(\beta_0/\alpha_0)
\operatorname{Ai}'(X)-E_{n,0}/(\varepsilon\alpha_0)$.
Use the nonzero Airy Wronskian
[DLMF 9.2.7](https://dlmf.nist.gov/9.2#E7), together with
$|\operatorname{Bi}(X)|\le C(1+|X|)^{-1/4}$ and
$|\operatorname{Bi}'(X)|\le C(1+|X|)^{1/4}$ from
[DLMF 9.7.9–9.7.12](https://dlmf.nist.gov/9.7#E9), with compact
intervals covered by continuity. Since
$\varepsilon\sqrt{1+|X|}\le\varepsilon+\sqrt{\zeta_0}$,
the Wronskian's error is uniformly $O(\varepsilon^3)$. Its other
factor has an upper bound $C(1+|X|)^{-1/4}$. Thus at these actual
middle nodes, including $X$ of negative order $n^{2/3}$,

$$
|\operatorname{Ai}'(X)|\ge c(1+|X|)^{1/4}. \tag{LC121}
$$

Subtract the complete common middle-row term, rather than assuming
an Airy zero. At the actual node this gives

$$
K_{n,d}=-\varepsilon^2D_d\operatorname{Ai}'(X)
+E_{n,d}-\frac{\alpha_d}{\alpha_0}E_{n,0},\qquad
\frac{|E_{n,d}-(\alpha_d/\alpha_0)E_{n,0}|}
 {\varepsilon^2|D_d\operatorname{Ai}'(X)|}=O(\varepsilon^2).
\tag{LC122}
$$

The exact determinant (LC111) and (LC116) imply
$K_{n,-1}K_{n,+1}<0$. Restoring the original rows multiplies
their product by the positive $e^{2nA_n(y)}$; the two parity
factors cancel. Therefore $I_{n,-1}I_{n,+1}<0$, with precisely
the original-node interpretation consumed by (LC47).

For $X\ge0$, the classical positive-axis envelopes and signs
$\operatorname{Ai}>0$, $\operatorname{Ai}'<0$ give
$\operatorname{Ai}(X)\ge c\mathcal M(X)$; see
[DLMF 9.7.5–9.7.6](https://dlmf.nist.gov/9.7#E5) and
[9.9(i)](https://dlmf.nist.gov/9.9#i). Both leading terms in
(LC120) are positive by (LC116); the remainder divided by
$c\varepsilon\mathcal M(X)$ tends uniformly to zero.
Thus $K_{n,0}>0$ there. Under (U), after reducing the fixed
band, $\zeta_n(y)\ge0$ is exactly $y\le y_e$. The resulting
statement under (U) is

$$
\begin{gathered}
n\ge N,\quad |y-y_e|\le\delta_0,\quad I_{n,0}(y)=0\\
\Longrightarrow\quad y>y_e\quad\hbox{and}\quad
I_{n,-1}(y)I_{n,+1}(y)<0.
\end{gathered} \tag{LC123}
$$

Take $\delta_0<1/8$. Since $y_e\to1/4$, the fixed intervals

$$
Y_{\rm bulk}=[1/4+\delta_0/2,\ 1/4+3\delta_0/4],\qquad
Y_{\rm out}=[1/4-3\delta_0/4,\ 1/4-\delta_0/2] \tag{LC124}
$$

both lie within the fold band specified by (U) for all sufficiently
large $n$. The first is a fixed compact subset of $(1/4,\infty)$,
so it overlaps (LC57). On the second, $t/r_n=1/y$ lies strictly
above $4+\eta$ for the fixed positive choice

$$
\eta=\tfrac12\left((1/4-\delta_0/2)^{-1}-4\right). \tag{LC125}
$$

It therefore overlaps the all-actual-positive-root exterior
exclusion (LC64). This is a fixed original-coordinate overlap,
not merely a shrinking-window comparison. “Supplying the common cubic domain by an existing analytic implicit theorem”
supplies (U). This application does not settle growing hard-edge
heights, initial degrees, complex roots,
the total real-root count, global collision propagation, RH, or
strict Robin for every $H>5040$.


## Supplying the common cubic domain by an existing analytic implicit theorem

The common-domain interface (U) is obtained by applying the complex
Banach-space analytic implicit-function theorem, rather than by
reproving generic cubic normal-form theory. The supplier is
A. D. Michal and D. H. Hyers, *Solutions of differential equations
as analytic functionals of the coefficient functions*, Acta Math.
**91** (1954), 75–86,
[DOI 10.1007/BF02393426](https://doi.org/10.1007/BF02393426),
Theorem 1 on printed p.80, with its proof on p.81; the
[original full text](https://projecteuclid.org/journalArticle/Download?urlid=10.1007/BF02393426)
provides the complex Banach-space statement. Its analytic
maps are between complex Banach spaces, and the unknown-variable
differential must be a solvable bounded linear isomorphism. The
following verifies that differential, the actual source-function
parameter ball, common injectivity and source coverage. It is an
ordinary-analysis application with no Lean certificate or claim
of mathematical originality.

### A fixed coordinate for the limiting phase

Write $H_*(\rho)=-\rho/4+2\sqrt\rho-\log\rho$,
$h_*=3-\log4$ and $k_*=256^{1/3}$. At $4$, the first two
derivatives vanish and $H_*'''(4)=-1/128$. The fixed local coordinate

$$
U_0(\rho)=(\rho-4)
\left(\frac{3(H_*(\rho)-h_*)}{(\rho-4)^3}\right)^{1/3},
\qquad Q_0=U_0^{-1} \tag{LC126}
$$

uses the removable quotient's negative real cube-root branch.
That quotient has value $-1/256$ at $4$, so
$U_0'(4)=-1/k_*\ne0$. The ordinary local holomorphic inverse
theorem gives $Q_0(0)=4$, $Q_0'(0)=-k_*$ and exactly
$H_*(Q_0(t))=h_*+t^3/3$. Fix $a>0$ sufficiently small so $Q_0$
is holomorphic and univalent on a neighborhood of
$\overline{D_a}$, and its image lies strictly inside the established
common source nonvanishing domain, away from $\rho=0$.

Let $\mathscr A_a$ be the complex Banach algebra of continuous
functions on $\overline{D_a}$ holomorphic in $D_a$, with the
supremum norm. The entire source function, rather than $n$, will
be the parameter in this fixed space.

### The verified linear inverse and one common parameter ball

For $g\in\mathscr A_a$ and $(W,c_1,c_0)\in\mathscr A_a\times\mathbb C^2$
define the continuous polynomial map

$$
\mathcal F(g;W,c_1,c_0)=W^3/3+c_1W+c_0-g. \tag{LC127}
$$

It is complex analytic. At
$(g_*;W_*,c_{1,*},c_{0,*})=(t^3/3;t,0,0)$ its differential in
the unknowns is $\mathcal L(V,\alpha,\beta)=t^2V+\alpha t+\beta$.
Its bounded inverse on the same fixed disk algebra is

$$
\mathcal L^{-1}g=
\left(\frac{g-g(0)-tg'(0)}{t^2},\ g'(0),\ g(0)\right),\qquad
\left\|\frac{g-g(0)-tg'(0)}{t^2}\right\|_a
\le3a^{-2}\|g\|_a. \tag{LC128}
$$

The quotient extends at zero. Cauchy's estimate gives
$|g'(0)|\le a^{-1}\|g\|_a$, and the boundary estimate for the
quotient gives the displayed norm bound by the maximum principle.
Thus no analytic radius is lost in inverting the differential.

Apply the published analytic implicit theorem with parameter
space $\mathscr A_a$, unknown space $\mathscr A_a\times\mathbb C^2$
and target space $\mathscr A_a$. It supplies an analytic solution
map $g\mapsto(W[g],c_1[g],c_0[g])$ on one ball
$\|g-g_*\|_a<\eta$. Choose once $0<\epsilon_0<a/16$.
By continuity, reduce this same ball so
$\|W[g]-t\|_a<\epsilon_0$ and $|c_1[g]|+|c_0[g]|\le1$
throughout it. Choose a Schwarz-conjugation-invariant ball;
the equation and reference solution commute with this conjugation.
Uniqueness of the analytic solution branch through the reference
point makes the solution map commute with it as well.

For the actual discrete source set $\delta=y-y_e(n)$ and
$g_{n,\delta}(t)=H_{n,y_e(n)+\delta}(Q_0(t))-h_*$. Exactly,

$$
g_{n,\delta}-g_*=
\mathcal L_n(Q_0)-2\sqrt{Q_0}
-(y_e(n)-1/4)Q_0-\delta Q_0. \tag{LC129}
$$

The common complex source convergence in (LC66) and $y_e\to1/4$
give, explicitly,

$$
e_n=\|g_{n,0}-g_*\|_a
\le\sup_{Q_0(\overline{D_a})}|\mathcal L_n-2\sqrt\rho|
+|y_e(n)-1/4|\,\|Q_0\|_a\longrightarrow0.
$$

With $M_0=\|Q_0\|_a$,
choose fixed $\Delta>0$ such that $2\Delta M_0<\eta/4$,
and then $N$ such that $e_n<\eta/4$ for $n\ge N$. Hence
$\|g_{n,\delta}-g_*\|_a<\eta/2$ simultaneously for all
$n\ge N$, $|\delta|<2\Delta$. Each $\delta\mapsto g_{n,\delta}$
is an affine complex analytic map into the same Banach space.
This supplies a common complex parameter band without assuming
any analytic interpolation of the discrete index $n$.

### Injectivity, inverse coverage and uniform norms

Write $W_{n,\delta}=W[g_{n,\delta}]$ and similarly for the two
scalar coefficients. On $D_{3a/4}$ the Cauchy estimate gives

$$
|W'_{n,\delta}-1|\le q_0:=4\epsilon_0/a<1/4. \tag{LC130}
$$

Integrating along the segment between two points in this convex
disk gives
$|W_{n,\delta}(t_1)-W_{n,\delta}(t_2)|\ge(1-q_0)|t_1-t_2|$.
Thus these maps are univalent on one common disk.
For $|s|<a/2$ and $|t|=3a/4$, the strict inequality
$|W_{n,\delta}(t)-t|<\epsilon_0<|t-s|$ lets Rouché's theorem
count exactly one preimage of $s$ there. The inverse
$V_{n,\delta}=W_{n,\delta}^{-1}$ is therefore jointly holomorphic
on the common product domain and satisfies
$|V_{n,\delta}(s)-s|<\epsilon_0$,
$|V_{n,\delta}(s)|<9a/16$.

Set $r=a/8$ and

$$
R_n(s,y)=Q_0(V_{n,y-y_e}(s)),\qquad
A_n(y)=h_*+c_{0,n}(y-y_e),\qquad
\zeta_n(y)=-c_{1,n}(y-y_e). \tag{LC131}
$$

The implicit equation is exactly (LC107) on
$|s|<4r$, $|y-y_e|<2\Delta$. Each $R_n(\cdot,y)$ is univalent
there and its image lies in $Q_0(D_{9a/16})$, strictly within the
source nonzero domain. If
$m_0=\min_{|t|\le3a/4}|Q_0'(t)|>0$ and
$M_1=\max_{|t|\le3a/4}|Q_0'(t)|$, then

$$
\frac{m_0}{1+q_0}\le|R_{n,s}|\le\frac{M_1}{1-q_0}. \tag{LC132}
$$

For coverage, fix $d>0$ with
$\overline{D(4,d)}\subset Q_0(D_{a/8})$. On this source disk
define $S_n(\rho,y)=W_{n,y-y_e}(U_0(\rho))$.
It is jointly holomorphic, $|S_n|<a/8+\epsilon_0<2r$, and
$R_n(S_n(\rho,y),y)=\rho$. After increasing $N$ so
$|\rho_e(n)-4|<d/2$,

$$
D(\rho_e(n),d/2)\subset D(4,d)\subset R_n(D_{2r},y)
\quad(n\ge N,\ |y-y_e|<2\Delta). \tag{LC133}
$$

The displayed construction bounds $R_n,R_{n,s}$, their reciprocal
magnitudes, $A_n,\zeta_n$ and the inverse coordinate $S_n$ on
the common domains. Cauchy estimates give uniform bounds for
every fixed order of mixed derivatives on nested smaller domains,
such as $|s|\le3r$, $|y-y_e|\le\Delta$ and
$|\rho-4|\le d/2$ for $S_n$. In particular, the bounded
$V_{n,\delta}$ on $D_{4r}$ also has the immediate mixed bounds
$|\partial_s^j\partial_\delta^\ell V_{n,\delta}|
\le Cj!\ell!r^{-j}\Delta^{-\ell}$ on the same nested domains.

It remains to check that this uniform construction is centered
at the exact finite fold, rather than merely near it. By source
coverage let $s_e=S_n(\rho_e,y_e)$. Differentiating (LC107) twice
at this point gives
$H_{\rho\rho}R_{n,s}^2+H_\rho R_{n,ss}=2s_e$.
Both source derivatives vanish at the actual fold, so $s_e=0$.
The first derivative then gives $\zeta_n(y_e)=0$.
The third derivative gives $h_{3,n}R_{n,s}(0,y_e)^3=2$;
real symmetry and $h_{3,n}<0$ select $R_{n,s}=-k_n$.
The mixed derivative with $H_{\rho y}=-1$ gives
$\zeta_n'(y_e)=-k_n$. Thus (LC108) and every clause of (U)
are supplied by the same exact source construction.

Consequently the fixed-band application (LC120)–(LC125) now
has its common-domain premise discharged in ordinary analysis.
There exist fixed $\delta_0>0$ and $N$ such that every actual
positive real middle-row Jensen node with
$n\ge N$ and $|r_n/t-y_e(n)|\le\delta_0$ satisfies the strict
adjacent-row comparison, and the half $r_n/t\le y_e(n)$ is
zero-free within that band. The band has the stated fixed
original-coordinate overlaps with (LC57) and (LC64).
No numerical starting degree, full-row real-rootedness, total
real-root count, complex-root exclusion, growing hard-edge
control, RH, or strict Robin for every $H>5040$ follows.
The newly supplied interface and its application remain without
Lean certification.

## A growing-height comparison from the unchanged Gamma–zeta source

Keep the original $F(z)=\Xi(\sqrt z)/\xi_0$, $r_n$, $\omega_n$ and
same-source $I_{n,d}$ of (LC49)–(LC51), for $d=-1,0,1$. The existing
compact bulk, fixed fold and outer exclusion are reused. The application
below isolates the exact Gamma factor as the phase and treats the zeta
factor on the original circle. It uses sectorial Stirling and the fixed
Gaussian remainder supplier already used in (LC53)–(LC55); neither generic
result is reproved. It is an ordinary-analysis source application,
without a Lean certificate, numerical starting degree or originality claim.

### A coarse strip bound and the source factor

The additional published supplier is the Euler–Maclaurin representation
[DLMF 25.2.8](https://dlmf.nist.gov/25.2.E8), with $\Re s>0$, $s\ne1$:

$$
\zeta(s)=\sum_{k=1}^N k^{-s}+\frac{N^{1-s}}{s-1}
-s\int_N^\infty\{x\}x^{-s-1}\,dx. \tag{LC134}
$$

On a lower semicircle write $u=\rho e^{-i\vartheta}$,
$0\le\vartheta\le\pi$, $A=\omega_n\sqrt\rho$ and

$$
s=1/2+i\omega_n\sqrt u
=1/2+A\sin(\vartheta/2)+iA\cos(\vartheta/2),
\qquad \sigma=\Re s\ge1/2.
$$

For $A\ge4$ and $\sigma\le2$, one has $|\Im s|\ge A/2$ and
$|s|\le2A$. Take $N=\lceil A\rceil$ in (LC134). The three terms are
bounded by $2\sqrt N$, $2\sqrt N/A$ and $4A N^{-1/2}$, respectively.
For $\sigma\ge2$, the Dirichlet series gives
$|\zeta(s)|\le\zeta(2)<2$. Thus, on this entire original semicircle,

$$
|\zeta(s)|\le C\sqrt A,
\qquad |\zeta(s)-1|\le3\,2^{-\sigma}\quad(\sigma\ge2).
\tag{LC135}
$$

The second bound is the sum–integral bound for the same Dirichlet series.
Neither bound is a reciprocal-zeta estimate, source-zero exclusion in the
critical strip, or RH premise.

Define the unchanged exact factorization

$$
G_n(u)=\frac{s(s-1)}{2\xi_0}\pi^{-s/2}\Gamma(s/2),
\qquad F(r_nu)=G_n(u)\zeta(s),\qquad
h^G_{n,y}(u)=yu+\frac1n\log G_n(u)-\operatorname{Log}u.
\tag{LC136}
$$

A branch for the logarithm is used only on the local saddle neighborhood.
The Gamma-only phase is an estimating interface to the same source;
$F$, the coefficient window and the actual row nodes are not changed.
On the upper semicircle use the conjugate of the lower original-source
integrand, since $F$ has real coefficients. It is unnecessary to assert
that the same right-half-plane Gamma approximation holds on both halves.

### Uniform finite saddles on an expanding parameter interval

There are fixed $Y_0>1$, $\kappa>0$ and $N$ for the parameter interval

$$
Y_0\le y\le Y_n:=\kappa n/\log n,\qquad n\ge N.
\tag{LC137}
$$

The constants may be reduced or increased in the order indicated below.
Put

$$
T_n(y)=\omega_n/\sqrt y,\qquad
\ell_n(y)=\log(T_n(y)/(2\pi)),\qquad
\eta_n(y)=T_n(y)/(4n).
$$

Uniformly on (LC137), (LC49) gives $T_n\ge c\sqrt{n/\log n}$,
$c\log n\le\ell_n\le C\log n$ and
$c/\sqrt y\le\eta_n\ell_n\le C/\sqrt y$. In a fixed disk about
$v=yu=1$, the sectorial Stirling expansion and its analytic derivatives
therefore give the exact saddle equation in the form

$$
u\partial_u h^G_{n,y}=0
\iff
v-1+i\eta_n\sqrt v\bigl(\ell_n+i\pi/2+\tfrac12\operatorname{Log}v\bigr)
+O(1/n)=0. \tag{LC138}
$$

The error and every fixed number of its $v$ derivatives are uniformly
$O(1/n)$ on a smaller fixed disk. Indeed,
$u\partial_u\log G_n=(s-1/2)\log(s/(2\pi))/4+O(1)$ there.
The sector remains separated from the negative real axis, and
$|s|\ge cT_n\to\infty$. The Gamma and elementary factors have no zero
or pole on that disk.

Choose $Y_0$ sufficiently large so that $\eta_n\ell_n$ is uniformly
small. The holomorphic inverse/implicit theorem at $v=1$ supplies a
unique finite lower saddle $u^G_n(y)=v_n(y)/y$ in that fixed disk, with

$$
v_n=1+(\pi/2)\eta_n-i\eta_n\ell_n
+O((\eta_n\ell_n)^2+1/n).
\tag{LC139}
$$

This uses a single uniformly small perturbation of the equation $v-1=0$,
not independent local existence without common bounds. Its derivatives
are bounded on the same disk, so the inverse is obtained on a common
neighborhood, for instance by Rouché and a derivative bound away from zero.
The error is smaller than a fixed fraction of $\eta_n\ell_n$ after
increasing $Y_0,N$. Therefore, with

$$
u^G_n=\rho_n e^{-i\theta_n},\qquad
\rho_n=|u^G_n|,
\qquad
c/y\le\rho_n\le C/y,\qquad
c/\sqrt y\le\theta_n\le C/\sqrt y,
\tag{LC140}
$$

one has $\theta_n>0$. Also $y\rho_n=1+O(y^{-1/2})$.
The actual Gamma-only angular curvature

$$
a^G_n=(u^G_n)^2\partial_u^2 h^G_{n,y}(u^G_n)
=1+O(y^{-1/2}),\qquad \Re a^G_n\ge1/2
\tag{LC141}
$$

is uniformly nondegenerate. These statements concern exact finite saddles;
no limiting-phase saddle is inserted into the original integral.

### Paying the full circle and the local substitution error

Fix a small angular $\beta>0$, then enlarge $Y_0$ so
$\theta_n<\beta/4$. On a fixed complex angular neighborhood of
$|\theta|\le2\beta$, the arguments of $s/2$ stay in a fixed Stirling
sector, including where $\Re s$ becomes negative after crossing the
positive $u$ axis. The Gamma factor has no pole there. With the angular
local phase $\phi^G(\theta)=h^G_{n,y}(\rho_n e^{i\theta})$, every fixed
positive-order derivative of $n^{-1}\log G_n$ is $O(y^{-1/2}+1/n)$.
Consequently, uniformly on this neighborhood, the Gaussian construction
(LC53) has a common disk and analytic inverse with bounded norms.
On the real angular interval the curvature satisfies

$$
\partial_\theta^2\Re\phi^G(\theta)\le-c_0<0
\quad(|\theta|\le2\beta),\qquad
\Re\phi^G(\theta)\le\Re\phi^G(-\theta_n)
-c_1(\theta+\theta_n)^2.
\tag{LC142}
$$

Here $\phi^{G\prime}(-\theta_n)=0$ exactly. The bound follows from
$-y\rho_n\cos\theta$ and the uniform small Gamma derivative correction.
The fixed-angle inverse and its maps need not preserve source zeta
nonvanishing across the axis: they are used only for the Gamma integrand.

On the rest of the lower semicircle, sectorial Stirling gives
$|n^{-1}\log|G_n||\le C y^{-1/2}+C\log n/n$.
The fixed decrease of $y\rho_n\cos\theta$ outside $|\theta|<\beta$
therefore yields a $c_2n$ exponent gap after increasing $Y_0$.
This uses the modulus of the Gamma factor itself, including its
real-frequency exponential attenuation, rather than the positive-kernel
triangle envelope.

For the original-source lower local arc

$$
-\theta_n-\beta\le\theta\le-\theta_n/2,
\tag{LC143}
$$

one has

$$
\Re s=1/2+\omega_n\sqrt{\rho_n}\,|\sin(\theta/2)|
\ge c_3\frac{n}{y\log n}.
\tag{LC144}
$$

The Dirichlet series and its first derivative are uniformly bounded
on this arc after choosing $\kappa$ small enough that (LC144) is at
least four. The polynomial bound (LC135) remains available on its
complement, where no source zeta nonvanishing is required.

The omitted original-source central arc $[-\theta_n/2,0]$ has an
exponent gap $c_5n\theta_n^2\ge c_6n/y$ by (LC142). Its zeta factor
has the polynomial bound (LC135). All other omitted lower arcs have
either this gap or the fixed $c_2n$ gap. Their normalized error is
$O(n^M e^{-c_7n/y})$, including the polynomial zeta bound and
$\sqrt n$ saddle normalization. The normalized $u^{-d}$ amplitudes
$\rho_n^du^{-d}$ have modulus one on the original circle.
Choose the fixed $\kappa$ sufficiently small, then $N$ sufficiently
large, so this relative error is at most $Cn^{-3}$ throughout (LC137).
This is possible because $n/y\ge\kappa^{-1}\log n$.

For the Gamma-only comparison integral, extend (LC143) to the fixed
centered arc $[-\theta_n-\beta,-\theta_n+\beta]$. The added part has
the same $c_6n/y$ gap by (LC142). No zeta approximation is asserted
on that added estimating arc, including its positive-axis crossing.
The fixed Gaussian chart converts the centered Gamma-only arc into
one fixed Gaussian segment and exponentially small connecting arcs
in uniformly interior descent sectors, as in (LC53). This pays the
Gamma comparison integral without applying a fixed-phase theorem
verbatim to an $n$-dependent source phase.

### Keep the exact source half-amplitude at the actual node

Choose $\sqrt{a^G_n}$ with positive real part and set the exact
Gamma Gaussian scale

$$
B^G_n(y)=\frac{\exp(nh^G_{n,y}(u^G_n))}{\sqrt{2\pi n a^G_n}}
\ne0.
\tag{LC145}
$$

The fixed-phase Gaussian supplier, with uniformly bounded normalized
analytic amplitudes and $M=1$, estimates the complete centered
Gamma-only arc by $B^G_n(1+O(1/n))$.
Instead of deleting the local zeta factor, retain the common exact
original-source half-amplitude

$$
\mathscr B_n(y)=\frac1{2\pi}
\int_{-\theta_n-\beta}^{-\theta_n/2}
 e^{n\phi^G(\theta)}
 \zeta(1/2+i\omega_n\sqrt{\rho_n e^{i\theta}})\,d\theta.
\tag{LC146}
$$

It is independently defined from the same source and contour for all
three offsets. Its nonvanishing on the saddle scale is the next
proof obligation; it is not assumed merely because it is named.

Let $Q_n(y)=n/(y\log n)$. Along the source arc (LC143), the
Dirichlet series gives
$|\zeta'(s)|\le C e^{-cQ_n}$, and $|\partial_\theta s|\le C A$.
For example, for $\sigma\ge4$, bound the derivative series by
$2^{-\sigma/2}\sum_{m\ge2}(\log m)m^{-2}$.
Every intermediate point along the real angular segment from the
saddle to the given point retains the same positive real-part floor.
Hence
$|\zeta(s(\theta))-\zeta(s(-\theta_n))|
\le C A e^{-cQ_n}|\theta+\theta_n|$.
The Gaussian first absolute moment from (LC142) is $O(1/n)$, so

$$
\frac{\mathscr B_n}{B^G_n}
=\zeta(s_n^G)+O\!\left(\frac1n+
\frac{A}{\sqrt n}e^{-cQ_n}+n^M e^{-c_7n/y}\right)
=\zeta(s_n^G)+O((\log n)^{-1/2}),
\quad s_n^G=1/2+i\omega_n\sqrt{u_n^G}.
\tag{LC147}
$$

Here $A/\sqrt n\asymp\sqrt{Q_n}/\sqrt{\log n}$ and
$\sqrt{Q_n}e^{-cQ_n}$ is bounded uniformly for $Q_n\ge c/\kappa$.
The final term includes the missing Gamma-only estimating arc.
At the exact saddle the same Dirichlet bound gives
$|\zeta(s_n^G)-1|\le3\,2^{-\Re s_n^G}\le1/4$ after reducing
$\kappa$. Therefore (LC147), for large $n$, supplies
$c|B^G_n|\le|\mathscr B_n|\le C|B^G_n|$. This nonzero lower bound
uses the Euler half-plane, not a critical-line zeta lower bound.

For $d=\pm1$, the lower original-source amplitude is $e^{-id\theta}$
after normalization by $\rho_n^d$. On the real arc,
$|e^{-id(\theta+\theta_n)}-1|\le|\theta+\theta_n|$.
Using (LC142), the bounded zeta series on the same source arc, and
its absolute first Gaussian moment gives the simultaneous exact-source
comparison

$$
\rho_n^d I_{n,d}(y)=2\Re(e^{id\theta_n}\mathscr B_n)+E_{n,d},
\qquad
|E_{n,0}|\le Cn^{-3}|B^G_n|,\qquad
|E_{n,\pm1}|\le Cn^{-1/2}|B^G_n|.
\tag{LC148}
$$

The $d=0$ error is only the complete original-circle complement;
there is no local approximation error for it. The $d=\pm1$ bounds
include both the local amplitude difference and that complement.
The upper contribution is the conjugate of the lower original-source
contribution. No extra zeta branch or unrelated neighboring phase is used.

At every actual positive middle-row node $I_{n,0}(y)=0$, (LC148)
and the independently established lower bound imply

$$
|\Re\mathscr B_n|\le Cn^{-3}|\mathscr B_n|,
\qquad |\Im\mathscr B_n|\ge\tfrac12|\mathscr B_n|.
\tag{LC149}
$$

The opposite neighboring leading terms now have size
$2|\Im\mathscr B_n|\sin\theta_n\asymp|\mathscr B_n|/\sqrt y$.
The two errors are $O(|\mathscr B_n|/\sqrt n)$, smaller by
$O(\sqrt{y/n})=O((\log n)^{-1/2})$ uniformly on (LC137).
Equivalently the same-row exact product identity gives

$$
\frac{I_{n,-1}(y)I_{n,1}(y)}{|\mathscr B_n(y)|^2}
=-4\sin^2\theta_n
+O\!\left(\frac{\sin\theta_n}{\sqrt n}+\frac1n\right)<0.
\tag{LC150}
$$

The powers $\rho_n^{-1}$ and $\rho_n$ cancel. The error divided by
the leading $\sin^2\theta_n\ge c/y$ is
$O(\sqrt{y/n}+y/n)$, which tends to zero uniformly.
Through (LC47) this is the original strict principal comparison
$\mathcal J_n'(t)\mathcal G_n(t)>0$ at every actual positive node
in the growing range. Both neighbors are nonzero; these nodes are
simple and have no indicated adjacent collision.

### Remaining growing source-height range

The moving lower height boundary is

$$
t\ge T_n^{\rm mov}:=\frac{r_n\log n}{\kappa n}
\sim\frac{16n}{\kappa\log n}.
\tag{LC151}
$$

The range joins (LC57) at fixed $y$ and, through the established fixed
fold and outer exclusion, controls every actual positive node with
$t\ge T_n^{\rm mov}$ for sufficiently large degrees. It does not
supply $0<t<T_n^{\rm mov}$ as this boundary tends to infinity.
The fixed-band result (LC30) retains its $\forall R\,\exists N_R$
quantifiers; it cannot cover a moving boundary by relabeling $R$.
At smaller heights the Gamma saddle's real-part displacement need
not stay in the above Euler half-plane, so its local nonzero amplitude
bound is a genuine remaining source obligation.

This application does not count all real roots, exclude complex
roots, supply a numerical starting degree, settle initial degrees or
global common-zero propagation, or prove RH or all-integer strict Robin.
It remains without Lean certification or a mathematical originality claim.

## Counting actual bulk roots without a complete-positive-row premise

Keep the unchanged source, normalization and degree-zero-shift family of
(LC46)–(LC51). The accepted compact-bulk estimates (LC52)–(LC57) are the
input; the original Gamma–zeta contour and Gaussian supplier are not
reproved. This is a source-specific application of those estimates,
Appell differentiation and real sign counting. It supplies neither a new
generic zero-distribution theorem, a literature originality claim nor
Lean certification.

The finite S-transform application (LC44) assumed an unbounded sequence
of entirely positive-root rows. The compact-bulk source estimates allow
a different inference: actual positive roots can be counted in every
fixed compact interval inside the limiting support, without assuming
that any complete row is real-rooted.

### Exact phase variation and the derivative at actual nodes

Fix $Y=[a,b]\subset(1/4,\infty)$. Use the exact finite lower saddle
$u_n(y)$, curvature $a_n(y)$ and common nonzero amplitude $B_n(y)$
of (LC52)–(LC55). Choose a continuous phase $\Theta_n$ with
$B_n(y)=|B_n(y)|e^{i\Theta_n(y)}$ on $Y$.

The same source's analytic derivative bounds and saddle
nondegeneracy give $u_n'(y)=-1/h_{n,y}''(u_n(y))$ and uniformly
bounded $u_n',a_n',a_n'/a_n$ on this fixed interval. These are
obtained by differentiating the exact saddle equation; no derivative
of the remainder in (LC55) is used. Since $\partial_yh_{n,y}(u)=u$
and $\partial_uh_{n,y}(u_n)=0$, the amplitude in (LC54) has

$$
\Theta_n'(y)
=n\Im u_n(y)-\tfrac12\Im\frac{a_n'(y)}{a_n(y)},
\qquad
\frac{\Theta_n'(y)}n\longrightarrow
-\frac{\sqrt{4y-1}}{2y^2}
\quad\text{uniformly on }Y.
\tag{LC152}
$$

In particular, $\Theta_n$ is strictly decreasing for sufficiently
large $n$, with a derivative bounded away from zero after division
by $n$. The continuous branch's additive multiple of $2\pi$ has no
effect on any phase difference below.

Reuse exact Appell differentiation, equivalently differentiating
(LC51) on a fixed Cauchy circle, to obtain
$\partial_y I_{n,0}(y)=nI_{n,-1}(y)$. Formula (LC55), with its
absolute error and the same $B_n,u_n$, gives

$$
\frac{I_{n,0}(y)}{2|B_n(y)|}
=\cos\Theta_n(y)+O_Y(n^{-1}),
\qquad
\frac{\partial_y I_{n,0}(y)}{2n|B_n(y)|}
=\Re u_n\cos\Theta_n-\Im u_n\sin\Theta_n+O_Y(n^{-1}).
\tag{LC153}
$$

At every actual real zero $I_{n,0}(y)=0$ in $Y$,
$|\cos\Theta_n(y)|\le C_Y/n$. Its phase is within $O_Y(n^{-1})$
of a unique $\pi/2+k\pi$. Since $-\Im u_n\ge c_Y>0$,

$$
\operatorname{sign}\bigl(\partial_y I_{n,0}(y)\bigr)
=\operatorname{sign}\bigl(\sin\Theta_n(y)\bigr),
\qquad \partial_y I_{n,0}(y)\ne0.
\tag{LC154}
$$

These statements are at actual coefficient zeros, without replacing
them by zeros of a leading cosine or assuming simplicity beforehand.

### One actual root in each complete phase interval

Consider a complete phase interval
$[k\pi,(k+1)\pi]\subset\Theta_n(Y)$. Strict monotonicity supplies
its two actual $y$ endpoints. By (LC153), the two endpoint values of
$I_{n,0}$ have opposite signs for large $n$, so there is a real root
between them. Every root in this interval has its phase near the
same midpoint and, by (LC154), its derivative has the same nonzero
sign. There is at most one such root: successive simple zeros of
a real differentiable function have alternating crossing directions.
Here $I_{n,0}$ is a nonzero polynomial in $y$, up to a positive
constant, so it has finitely many zeros. Consequently there is
exactly one root per complete phase interval. Each of the two
possibly incomplete endpoint phase intervals contains at most one.

Let $N_n(Y)$ count actual zeros with $r_n/t\in Y$, including
multiplicity. All these bulk zeros are simple by (LC154).
Endpoint conventions change the count by at most two. Thus

$$
N_n(Y)=\frac{\Theta_n(a)-\Theta_n(b)}\pi+O(1),
\qquad
\frac{N_n(Y)}n\longrightarrow
\int_a^b\frac{\sqrt{4y-1}}{2\pi y^2}\,dy.
\tag{LC155}
$$

The $O(1)$ counting discrepancy is independent of $n$ for fixed $Y$;
it is not a rate for the phase convergence in (LC152).

For any fixed $0<\alpha<\beta<4$, put
$Y=[1/\beta,1/\alpha]$. The actual-source correspondence (LC46)
and the substitution $x=1/y$ give

$$
\frac1n\#\{t>0:\mathcal J_n(t)=0,
                  \alpha\le t/r_n\le\beta\}
\longrightarrow
\int_\alpha^\beta\frac1{2\pi}\sqrt{\frac{4-x}{x}}\,dx.
\tag{LC156}
$$

This holds along every sufficiently large degree, rather than only
along a hypothetical complete-positive-root subsequence. It counts
actual simple positive roots in the displayed compact bulk interval.

### What the count supplies, and what it leaves open

The density in (LC156) is the same probability density of
$\mathrm{MP}_1$ in (LC44). Let $N_n^+$ denote the total number of
positive real roots of $\mathcal J_n$, with multiplicities. Because
$a_n>0$, the polynomial has degree $n$. Also
$\mathcal J_n(t)>0$ for every $t\le0$, so it has no nonpositive
real roots. The lower count in (LC156), followed by
$\alpha\downarrow0$, $\beta\uparrow4$, and the degree upper bound
$N_n^+\le n$, yields

$$
\frac{N_n^+}{n}\longrightarrow1,
\qquad n-N_n^+=o(n).
\tag{LC157}
$$

Thus the number of nonreal roots is $o(n)$, without excluding any
individual nonreal root. No numerical starting degree or quantitative
rate is supplied.

Equations (LC156)–(LC157) also give weak convergence to
$\mathrm{MP}_1$ of the empirical measure of all $n$ complex roots,
counting multiplicities and viewing this real limiting measure on
$\mathbb C$. Explicitly, with the sum over all actual complex roots,

$$
\mu_n=\frac1n\sum_{\mathcal J_n(z)=0}\delta_{z/r_n}
\ \Longrightarrow\ \mathrm{MP}_1.
\tag{LC158}
$$

Indeed the positive-root measure has the stated counts
on every compact subinterval of $(0,4)$ and total mass tending to one;
the remaining roots carry mass $o(1)$. Test bounded continuous
functions first on $[\alpha,\beta]$, then use the degree bound to
make the mass of its complement arbitrarily small. This does not
supply convergence of unbounded moments, exclude complex outliers,
or put every root on the real line.

The all-positive-subsequence premise is unnecessary for this weak
law, because the present source-specific contour input supplies
actual real-root counts. The earlier conditional finite S-transform
application remains within its stated hypotheses and is not reproved.
An $o(n)$ defect can still contain nonreal roots for arbitrarily large
$n$; their mass can disappear from a weak limit. The result therefore
does not prove RH or strict Robin for all $H>5040$, settle the
uniform actual-node comparison in $0<t<T_n^{\rm mov}$, close initial
degrees or global common-zero propagation, or localize every nonreal
root. These are still full-criterion obligations.

## Nonreal-root defect and the actual critical-value word

Reuse the unchanged coefficient source, its positive coefficients,
(LC46)–(LC47), the actual normalized reflection $q_n$ and the exact
primitive/constant identity in
[SourceJensenIntegralExtension](../../Blueprint/D5/S3/Zeros/Jensen/SourceJensenIntegralExtension.md).
Classical Rolle counting with multiplicity and root counting between
real critical points are used as suppliers; no new generic Sturm,
Rolle or polynomial-root theorem is asserted. The application below
tracks the actual source row, even when that row is not entirely real.
It has no Lean certificate or literature originality claim.

[Craven–Csordas, *Jensen polynomials and the Turán and Laguerre
inequalities*](https://doi.org/10.2140/pjm.1989.136.241), Theorem 2.5
(iii)–(v), printed pp.248–249, already provides the finite-tower strict
neighboring-node criterion. It requires the comparisons at all preceding
rows; it does not make one isolated comparison a full-root-count proof.
[Craven–Csordas, *Complex zero decreasing sequences*](https://doi.org/10.4310/maa.1995.v2.n4.a4),
Corollary 3.2 in the [author archive](https://math.hawaii.edu/~tom/mathfiles/zds.pdf),
PDF p.15, with the identity sequence, multiplication by $n!$ and
positive variable rescaling, supplies the unchanged finite Jensen
multipliers $(n)_{\underline k}/n^k$ for $k\le n$ and zero afterward.
These are reused published suppliers. The ledger below only connects
classical critical-value counting to the actual mixed rows and the
already obtained $o(n)$ count; it introduces no new Jensen criterion or
complex-zero-decreasing theorem.

### A monotone integer that a weak root law cannot eliminate

For $n\ge1$ put

$$
\alpha_n=\frac{n}{n+1},\qquad
q_n(x)=x^n\mathcal J_n(1/x),\qquad
q_{n+1}'(x)=(n+1)\alpha_n^n q_n(x/\alpha_n).
\tag{LC159}
$$

The expression at zero is its polynomial continuation, not division
by zero. Source normalization $a_0=1$ makes $q_n$ monic of degree $n$;
$q_n(0)=\beta_n=(-1)^n n!a_n/n^n\ne0$. Coefficient positivity
excludes nonpositive real roots. The reflection identifies positive
roots and multiplicities with those of $\mathcal J_n$.

Write $N_n^+$ for the number of real positive roots with multiplicity
and $\Delta_n=n-N_n^+$ for the number of nonreal roots. Rolle's theorem
with multiplicity gives at least $N_{n+1}^+-1$ real roots of
$q_{n+1}'$ whenever $N_{n+1}^+\ge1$. The exact positive scaling in
(LC159) identifies its real-root count with $N_n^+$. If
$N_{n+1}^+=0$ the resulting bound is automatic. Hence

$$
N_{n+1}^+\le N_n^++1,\qquad
0\le\Delta_n\le\Delta_{n+1},\qquad
\Delta_n\in2\mathbb Z_{\ge0}.
\tag{LC160}
$$

Evenness follows from complex conjugate pairing, counted with
multiplicity. Thus a nonreal-root defect cannot disappear at a later
degree of this exact derivative tower. This is a count, not a claim
that individual nonreal roots follow specified trajectories.

By (LC157), $\Delta_n=o(n)$ nonetheless. A nondecreasing even integer
sequence can remain positive while its ratio to $n$ vanishes, so these
two conclusions do not force $\Delta_n=0$.

### The exact ledger includes multiple critical points and zero values

List all distinct positive real roots of $q_n$ as
$\lambda_1<\cdots<\lambda_k$, with multiplicities $m_i\ge1$.
The list may be empty. Then $\sum_i m_i=N_n^+$ and, by (LC159),
all real critical points of $q_{n+1}$ are
$c_i=\alpha_n\lambda_i$, with the same derivative multiplicities $m_i$.
Set

$$
v_i=q_{n+1}(c_i),\qquad
s_i=\operatorname{sign}(v_i),\qquad
s_0=(-1)^{n+1},\qquad s_{k+1}=1.
$$

The two end signs are the actual constant's sign at zero and the
monic polynomial's sign at positive infinity. Define
$C_n=\#\{0\le i\le k:s_i s_{i+1}<0\}$, and
$Z_n=\{i:1\le i\le k,\ v_i=0\}$.

Between consecutive real critical points the derivative is nonzero,
so the polynomial is strictly monotone. Such an open interval has
exactly one root when its two nonzero end signs are opposite and
none otherwise. A zero critical value instead gives a root exactly
at $c_i$, with multiplicity $m_i+1$, by the local order relation
between a polynomial and its derivative. These roots are not counted
again in the open intervals. Consequently the actual-source ledger is

$$
N_{n+1}^+
=C_n+\sum_{i\in Z_n}(m_i+1),\qquad
\Delta_{n+1}-\Delta_n
=1+\sum_{i=1}^k m_i-C_n-\sum_{i\in Z_n}(m_i+1).
\tag{LC161}
$$

This includes stationary inflections, repeated previous-row real roots
and common zeros. When $k=0$, the derivative has no real zero; the end
signs give exactly one real root, since then $n$ is even, and the defect
is unchanged. Adjacent critical points cannot both have zero values,
because the polynomial is strictly monotone between them. No assertion
that such degeneracies occur for the actual source is made.

The quantities on the right are previous-row real critical nodes,
source critical values and multiplicities, independently of any
assumed root count of the target row. They still require certification;
the formula is not a uniform estimate or an efficient root algorithm.

### Simple nonzero critical values: wrong actual nodes are isolated

Suppose for this degree that all real roots of $q_n$ are simple and
all $v_i$ are nonzero. No assumption is imposed on its nonreal roots.
Now $k=N_n^+$ and $n-k$ is even. The desired alternating critical
sign is $(-1)^{n+1-i}$. Define a bit $\varepsilon_i$ by

$$
\varepsilon_i=0\ \Longleftrightarrow\
\operatorname{sign}(v_i)=(-1)^{n+1-i},\qquad
\varepsilon_0=\varepsilon_{k+1}=0.
$$

Consecutive actual end signs differ exactly when the consecutive bits
are equal. Each maximal run of $1$ bits has two transitions, because
the two endpoint bits are zero. If $b_n$ counts these maximal runs,
(LC161) therefore becomes

$$
\Delta_{n+1}-\Delta_n
=\#\{0\le i\le k:\varepsilon_i\ne\varepsilon_{i+1}\}
=2b_n.
\tag{LC162}
$$

The binary-word identity alone allows longer runs, but actual critical
values forbid adjacent wrong bits. Put
$\tau_i=\operatorname{sign}q_n'(\lambda_i)=(-1)^{k-i}$.
On $(c_i,c_{i+1})$ the derivative of $q_{n+1}$ has this sign, so
$\tau_i(v_{i+1}-v_i)>0$. Two wrong bits would instead give
$\operatorname{sign}v_i=\tau_i$ and
$\operatorname{sign}v_{i+1}=-\tau_i$, a contradiction.
Every realizable wrong run is therefore a singleton:
$b_n=\#\{i:\varepsilon_i=1\}$.
Under the displayed simple/nonzero assumptions, each wrong actual
critical node contributes one conjugate pair to the defect increase.
This assigns no trajectories or locations to those roots. Zero critical
values and multiplicities use (LC161), rather than being silently
assigned bits in (LC162).

At the original actual node $t_i=1/\lambda_i$, reuse the same source's
adjacent identity. The exact quantities are

$$
q_n'(\lambda_i)=-\lambda_i^{n-2}\mathcal J_n'(t_i),\qquad
v_i=\frac{\alpha_n^{n+1}}n\lambda_i^n\mathcal G_n(t_i),\qquad
q_n'(\lambda_i)v_i
=-\frac{\alpha_n^{n+1}}n\lambda_i^{2n-2}
       \mathcal J_n'(t_i)\mathcal G_n(t_i).
\tag{LC163}
$$

The sign of $q_n'(\lambda_i)$ is $(-1)^{k-i}$; the nonreal conjugate
factors are positive on the real axis. Because $k\equiv n\pmod2$,
$\varepsilon_i=0$ is exactly the already prescribed strict principal
comparison $\mathcal J_n'(t_i)\mathcal G_n(t_i)>0$.
This correspondence uses every actual real root, not a complete
$n$-node arrow matrix. That full arrow representation's original
complete-real-critical-node hypothesis is not supplied by this ledger.

### Defect births are sparse, and their witnesses are in the unpaid range

The unconditional count (LC160), evenness and (LC157) give

$$
\#\{1\le n\le M:\Delta_{n+1}>\Delta_n\}
\le\frac{\Delta_{M+1}-\Delta_1}{2}
=o(M).
\tag{LC164}
$$

This conclusion needs no simplicity or nonzero-critical-value
assumption. It bounds the number of degrees at which the count
increases; it neither proves that their number is finite nor rules
out a single increase.

If the strict original principal comparison holds at every actual
positive $\mathcal J_n$ node in one degree, (LC163) makes all the real
critical nodes simple with nonzero values and every bit zero.
Equation (LC162) then gives $\Delta_{n+1}=\Delta_n$.

For each fixed $R>0$, (LC30) pays this strict comparison at
$0<t\le R$ for all sufficiently large $n$; (LC151) pays it at
$t\ge T_n^{\rm mov}$. Thus, for all sufficiently large $n$ depending
on $R$, an increase in the defect requires an actual positive node
in the uncovered interval

$$
R<t<T_n^{\rm mov}=\frac{r_n\log n}{\kappa n}
\quad\text{at which}\quad
\mathcal J_n'(t)\mathcal G_n(t)\le0.
\tag{LC165}
$$

The non-strict failure includes repeated real nodes or a zero adjacent
value; neither is assumed absent. A failure of the strict comparison
does not by itself imply a defect increase in a degenerate step;
(LC161) gives that step's exact count.

The literature's existing finite-degree coverage supplies
$\Delta_n=0$ for $n\le9\cdot10^{24}$ under the actual coefficient
correspondence in
[the Jensen supplier](../Zeros/osullivan2021modifiedjensen.md#known-finite-degree-coverage-from-verified-zero-height).
Eliminating every later increase would preserve zero defect at every
degree and pay the classical Jensen/RH criterion. The sparse-degree
bound and the localization of a possible witness do not eliminate
those increases. No degree threshold for the new comparisons has
been placed inside that finite verified range. RH, strict Robin for
all $H>5040$, the uniform lower-range comparison and individual
complex-root exclusion remain unresolved.

## A no-separation source capture bound and its finite-degree obstruction

Keep the same entire source $F(z)=\Xi(\sqrt z)/\xi_0$, $F(0)=1$,
positive coefficients $a_k$, zero coefficient shift and finite Jensen
multipliers of (LC17) and (LC46). Reuse the already checked
Craven–Csordas finite-tower criterion and complex-zero-decreasing
supplier cited above, rather than introduce another generic Jensen or
root-count theorem. The additional published supplier is Matthew Buck,
[*Integer points of meromorphic functions*](https://doi.org/10.1017/S0013091513000436),
Lemma 2.4, equation (2.2), and Remark 2.3, printed pp.369–370.
The source-specific application below has no Lean certification or
literature originality claim.

The fixed-real-cluster interface (LC27) uses a chosen isolation radius
and an unevaluated positive source floor on its circle. The bound here
instead captures nonreal source clusters, without separating their
individual zeros, using only positive-axis source upper bounds. It does
not replace the real-cluster Hermite margins or prove the low-range
strict comparison.

### Exact finite Jensen error and the published exceptional-disc floor

Put

$$
G(x)=F(-x)=\sum_{k\ge0}a_kx^k
=\frac{\xi(1/2+\sqrt x)}{\xi_0},\qquad x\ge0,
\qquad
\max_{|z|\le x}|F(z)|=G(x).
\tag{LC166}
$$

The maximum follows from coefficient positivity and equality at $z=-x$.
For $R\ge1$, the complex triangle-inequality version of the existing
(LC17) gives the same finite-multiplier error; the ordinary Cauchy
second-derivative bound on the circle of radius $2R$ centred at $2R$
then gives

$$
\sup_{|z|\le2R}|\mathcal J_n(z)-F(z)|
\le\frac{(2R)^2G''(2R)}{2n}
\le\frac{G(4R)}n.
\tag{LC167}
$$

This uses the unchanged finite weights, including their zero tail at
$k>n$; it is not an error estimate for a shifted coefficient source.

Let $0<h\le R$ and set

$$
K(R,h)=6+\frac{\log(384R/h)}{\log2},\qquad
\mathcal N(R,h)
=\left\lfloor G(4R)G(8R)^{K(R,h)}\right\rfloor+1.
\tag{LC168}
$$

Use the standard Nevanlinna normalization
$T(r,u)=m(r,u)+N(r,u)$, with the proximity average of $\log^+|u|$.
Apply Buck's lemma to $u=1/F$, $s=R$, $m=0$ and
$\epsilon=h/(384R)$. These satisfy $s\ge1$ and $0<\epsilon\le1$;
$1/F$ is meromorphic on the required disk. Since $F(0)=1$, the
classical Jensen/first-main-theorem identity has zero additive constant:

$$
T(8R,1/F)=T(8R,F)\le\log G(8R).
\tag{LC169}
$$

Thus there is a finite union $U$ of open discs of total radius at most
$24\epsilon R=h/16$, outside which, for $|z|\le2R$,

$$
|F(z)|\ge G(8R)^{-K(R,h)}>0.
\tag{LC170}
$$

Every source zero in this region lies inside $U$. By the merging rule
in Buck's Remark 2.3, intersecting discs can be replaced by disjoint
open discs without increasing the total radius. Enlarging their union
retains (LC170) on its complement. No lower bound for $|\zeta|$ on a
critical-line or critical-strip contour is assumed.

### Joint capture with multiplicity, including arbitrarily close zeros

Write
$\Omega(R,h)=\{z:|z|\le R,\ |\Im z|\ge h\}$ and let
$\nu_P(E)$ count zeros of $P$ in $E$, with multiplicity.
Select the merged discs containing the source zeros in $\Omega(R,h)$.
Each selected disc has radius at most $h/16$. Every point of it is
within $h/8$ of a source zero it contains, and hence belongs to
$\Omega(R+h/8,7h/8)$; its closure lies in $|z|<2R$ and avoids the
real axis. Its boundary is outside $U$ and satisfies (LC170).

For every integer $n\ge\mathcal N(R,h)$, the definition of the floor
in (LC168) makes
$G(4R)/n<G(8R)^{-K(R,h)}$. Equations (LC167) and (LC170) therefore
supply the strict boundary inequality for the classical Rouché theorem
on each selected disc. The two functions have exactly the same zero
count in each one. In particular,

$$
\nu_{\mathcal J_n}\bigl(\Omega(R+h/8,7h/8)\bigr)
\ge\nu_F\bigl(\Omega(R,h)\bigr),
\qquad n\ge\mathcal N(R,h).
\tag{LC171}
$$

Multiplicity and close zero clusters are retained together inside a
disc; there is no minimum source-zero spacing or simple-zero premise.
Additional polynomial zeros outside the selected discs are not
controlled. In particular, this is a forward capture statement,
not a converse location statement for every nonreal polynomial zero.

The source upper-growth estimate already used after (LC50), with
$x=\sqrt{8R}$, gives

$$
\log\mathcal N(R,h)
=O\!\left(\sqrt R\log(R+2)\,[1+\log(R/h)]\right).
\tag{LC172}
$$

No new Stirling theorem or source asymptotic is needed. For every fixed
$A\ge0$, if $R_n\to\infty$, $h_n=R_n^{-A}$ and

$$
R_n=o\!\left(\frac{(\log n)^2}{(\log\log n)^4}\right),
\tag{LC173}
$$

then $\log\mathcal N(R_n,h_n)=o(\log n)$, so (LC171) eventually
applies jointly at $(n,R_n,h_n)$. This range does not reach the moving
actual-node boundary (LC151), and it controls no strict signs in real
zero clusters or in the thinner band $|\Im z|<h_n$.

### An off-line source zero forces a bounded-degree defect birth

Suppose, conditionally, that
$\tau=T+i\eta$, $T>0$, $0<|\eta|<1/2$, is a zero of $\Xi$.
It corresponds to a zeta zero $1/2-\eta+iT$. For the actual source,
$z_0=\tau^2$ and its conjugate are distinct nonreal zeros. Take

$$
R=\max\{1,T^2+\eta^2\},\qquad h=2T|\eta|,
\qquad 0<h\le R.
\tag{LC174}
$$

Equation (LC171) gives $\Delta_n\ge2$ for every
$n\ge\mathcal N(R,h)$, with $\Delta_n$ as in (LC160).
Since $\Delta_1=0$ and this integer defect is nondecreasing, its first
increase exists. Define

$$
b_\Delta=\min\{m\ge1:\Delta_{m+1}>\Delta_m\},
\qquad b_\Delta\le\mathcal N(R,h)-1.
\tag{LC175}
$$

The already established critical-value ledger implies that at this
actual degree there is a positive $\mathcal J_{b_\Delta}$ node with
$\mathcal J_{b_\Delta}'(t)\mathcal G_{b_\Delta}(t)\le0$; otherwise
all strict comparisons would preserve its defect. This implication
allows a repeated node or a zero critical value. It does not assert
that the integer step must pass through a multiple root. Nor does it
identify this real witness as a trajectory ancestor of the captured
complex zero, or imply $t\asymp T^2$.

If this degree is beyond the existing fixed-band and moving-range
thresholds, (LC165) places its witness between each already paid fixed
$R_0$ and $T_{b_\Delta}^{\rm mov}$. There is no numerical threshold
placing that condition inside the literature's finite verified range.
The earlier strict-comparison criterion can separately bound the first
strict failure, which can precede a defect increase in a degenerate
step; the two notions are not silently identified.

Conversely, a certified zero defect through a degree $D$ excludes
source zeros in any $\Omega(R,h)$ with $\mathcal N(R,h)\le D$.
This is a conditional certificate-consumption rule, not an extension
of the existing numerical verified range. The dependence on distance
from the real axis is explicit; no source-zero separation constant is
hidden in it.

The finite-source capture and its finite-degree obstruction do not
exclude a hypothetical off-line zero. They leave open the uniform
actual-node comparison in $0<t<T_n^{\rm mov}$, individual nonreal-root
exclusion, RH and strict Robin for every integer $H>5040$. The new
application remains ordinary analysis without Lean certification or
an originality assertion.

## Local source-relative error and polynomial conditional capture

Keep the original $F$, $\mathcal J_n$, positive $a_k$ and zero
coefficient shift. Reuse the exact Cauchy/Appell interface, the fixed
Gaussian estimates and sectorial Stirling already used in this note.
The Euler–Maclaurin supplier (LC134), the checked functional equation
[DLMF 25.4.2](https://dlmf.nist.gov/25.4.E2), Buck's Lemmas 2.1 and 2.4
and disc-merging rule, Titchmarsh's Theorem 9.6(A), and the
[DLMF digamma expansion 5.11.2](https://dlmf.nist.gov/5.11.E2) are
the published inputs. No generic saddle, Gaussian, Cartan or
zero-count theorem is reproved. This is an ordinary
source application, without Lean certification or an originality claim.

The global error in (LC167) ignores the original source's Gamma
attenuation near a high real frequency. The local estimate below keeps
that attenuation and a contour-specific relative source bound, with a
separate payment for the remote circle. It improves a conditional detection bound, not the all-node strict sign
criterion or a numerical zero verification.

### Two exact contour moments before any estimate

For $n\ge1$ and complex $t$, put

$$
\mathcal K_n(\theta)=\frac{n!}{2\pi n^n}
             e^{ne^{i\theta}-in\theta},\qquad
\mathcal J_n(t)=\int_{-\pi}^{\pi}
             \mathcal K_n(\theta)F(te^{i\theta})\,d\theta,
\qquad
\int_{-\pi}^{\pi}\mathcal K_n=1,
\qquad
\int_{-\pi}^{\pi}\mathcal K_n(e^{i\theta}-1)=0.
\tag{LC176}
$$

The first formula is the existing coefficient integral on $|v|=n$.
The last two identities take the constant and linear coefficient
moments of that same integral. They are exact, including the finite
Jensen truncation; no shifted source or approximate Gaussian measure
is substituted.

For $t\ne0$, $0<r\le|t|$, set
$M_t(r)=\max_{|z-t|\le r}|F(z)|$. Subtract
$F(t)+tF'(t)(e^{i\theta}-1)$ using both exact moments.
On $|\theta|\le r/(2|t|)$, the ordinary Cauchy Taylor bound gives
remainder at most $2M_t(r)|t|^2\theta^2/r^2$.
The already used fixed Gaussian norm bounds for this phase give
$\int|\mathcal K_n|\theta^2\le C/n$ and remote mass at most
$C\sqrt n\exp(-cnr^2/|t|^2)$. These follow with the same Stirling
normalization and fixed real-circle decrease; no moving source phase
is used. On the remote arc retain the exact source maximum (LC166)
and the Cauchy first-derivative bound. Thus the actual source has

$$
|\mathcal J_n(t)-F(t)|
\le \frac{CM_t(r)|t|^2}{nr^2}
+C\sqrt n e^{-cnr^2/|t|^2}
       \left[G(|t|)+M_t(r)\left(1+\frac{|t|}r\right)\right].
\tag{LC177}
$$

Here and below positive constants are universal for the fixed source
and fixed windows, independent of degree, height, off-line distance,
source multiplicities and source-zero spacings. Their numerical
values are not certified in this application.

### Uniform fixed-window bounds from existing source suppliers

Let $T\ge32$, $Q=T+2$ and $E_T=e^{-\pi T/4}$.
For $\Re s\ge1/2$ with a bounded real part and $|\Im s|\ge16$,
the calculation from (LC134), now with $N=\lceil|\Im s|\rceil$,
gives $|\zeta(s)|\le C\sqrt{1+|\Im s|}$; for $\Re s\ge2$ the
Dirichlet series gives the stronger constant bound. For $\Re s<1/2$
use the checked functional equation and sectorial Stirling to obtain
$|\chi(s)|\le C(1+|\Im s|)^{1/2-\Re s}$. Applying the same
positive-half-plane estimate to $1-s$ gives the coarse uniform result

$$
|\zeta(s)|\le C Q^{15}
\quad\left(-14\le\Re s\le18,\quad |\Im s-T|\le16\right).
\tag{LC178}
$$

This is a parameter application of (LC134) and the functional equation,
not an interpolation of pointwise fixed-$\sigma$ asymptotics. In
particular, DLMF 25.9.1's fixed-$\sigma$ convention is not used as a
uniform-strip theorem.

Write the exact Gamma factor as

$$
\mathcal A(s)=\frac{s(s-1)}{2\xi_0}\pi^{-s/2}\Gamma(s/2),
\qquad
\Phi(s)=-(s-1/2)^2,
\qquad F(\Phi(s))=\mathcal A(s)\zeta(s)=\xi(s)/\xi_0.
\tag{LC179}
$$

The last equality is the even entire power-series identity, requiring
no global square-root branch. The existing Stirling supplier on the
fixed window $|s-(1/2+iT)|\le2$ gives
$|\mathcal A(s)|\asymp E_TQ^{\Re s/2+3/2}$.
In particular its upper bound is $CE_TQ^3$, and its lower bound on
$|s-(1/2+iT)|\le1$ is $cE_T$. It has neither a zero nor a pole
in these high windows.

### Euler-anchored floor, zero count and chosen contour clearance

Suppose conditionally that
$\rho=1/2-\eta+iT$ is a zeta zero, with
$T\ge32$ and $0<|\eta|<1/2$. Set $L=\log Q$ and
$B_\eta=1+\log(1/|\eta|)$.
Normalize the auxiliary observation
$p_T(w)=\zeta(2+iT+w)/\zeta(2+iT)$.
The Euler product gives
$1/\zeta(2)\le|\zeta(2+iT)|\le\zeta(2)<2$.
This normalization does not replace $F$ in $\mathcal J_n$.
The disk $|w|\le16$ avoids the zeta pole, $p_T(0)=1$, and
(LC178) provides a universal $C_Z\ge1$ such that, with
$V_T=C_ZQ^{15}$,

$$
T(16,1/p_T)=T(16,p_T)\le\log V_T,
\qquad
1\le m_T\le n(4,1/p_T)\le\frac{\log V_T}{\log4}=O(L).
\tag{LC180}
$$

Here $T(r,\cdot)$ is the Nevanlinna characteristic, and
$m_T$ counts all nontrivial zeros with $|\Im\rho'-T|\le2$,
with multiplicity. They lie in $|w|<4$ since $0<\Re\rho'<1$.
The count bound is the existing Jensen inequality, also given in
Buck's Lemma 2.1 applied to $1/p_T$ with outer radius $16$,
inner radius $4$ and $p_T(0)=1$. Here $n(r,u)$ counts poles
of $u$ with multiplicity, so the reciprocal counts the source zeros. The lower count follows from the conditional target zero.
No new Riemann--von Mangoldt estimate is proved.

Apply Buck's Lemma 2.4 to $1/p_T$ at scale $2$, with $m=0$ and
$\epsilon=|\eta|/3072$. Put

$$
K_\eta=6+\frac{\log(3072/|\eta|)}{\log2},\qquad
 d=\frac{|\eta|}{64m_T}.
\tag{LC181}
$$

Its exceptional open discs have total radius at most $|\eta|/64$.
Outside them, for $|w|\le4$, one has
$|\zeta(2+iT+w)|\ge cV_T^{-K_\eta}$.
Add a disc of radius $d$ about each distinct zero counted by $m_T$.
Their total radii are at most $|\eta|/64$ even with multiplicities.
Merge the complete finite union by Buck's rule, without increasing
its total radius. Its complement retains both the lower floor and
clearance at least $d$ from every counted zero.

Let $D$ be the resulting open disc containing the target $\rho$.
Its radius is at most $|\eta|/32$, so its closure is within
$|\eta|/16$ of $\rho$, inside $|s-(1/2+iT)|<1$, and away from
the critical line. Its boundary lies outside the enlarged union.
Consequently

$$
|F(\Phi(s))|\ge cE_TV_T^{-K_\eta},\qquad
\operatorname{dist}\bigl(s,\{\rho':|\Im\rho'-T|\le2\}\bigr)\ge d,
\quad s\in\partial D.
\tag{LC182}
$$

The distance is created by the chosen contour. It is not a minimum
spacing between source zeros. Close zeros and their multiplicities
may remain together inside $D$.

### Reuse the published local logarithmic derivative

The additional classical supplier is E. C. Titchmarsh,
[*The Theory of the Riemann Zeta-Function*, second edition, revised
by D. R. Heath-Brown](https://sites.math.rutgers.edu/~zeilberg/EM18/TitchmarshZeta.pdf),
Theorem 9.6(A), equation (9.6.1), printed p.217 (PDF page 113).
It gives, uniformly for $-1\le\Re s\le2$ away from the zeros,

$$
\frac{\zeta'}{\zeta}(s)
=\sum_{|\Im\rho'-\Im s|\le1}\frac1{s-\rho'}+O(\log\Im s).
\tag{LC183}
$$

This is an unconditional local formula, with actual multiplicities;
no RH premise or replacement logarithmic-derivative proof is used.
The inspected second-edition PDF has SHA-256
`ee495ba7e6b7af4722317baa79087881c16f648cb8af72843eb869c7497a03d0`.
The strict versus non-strict ordinate cutoff makes no difference
here: its endpoint terms are bounded and there are $O(L)$ of them.

For $s\in\partial D$, the disc $|u-s|\le d/4$ has clearance
at least $3d/4$ from each counted zero. It stays in the stated strip
and near height $T$; every zero in the local sum belongs to the count
$m_T$. Equations (LC180)--(LC183) therefore give
$|\zeta'/\zeta(u)|\le C L^2/|\eta|$ on that disc.
The sectorial digamma expansion DLMF 5.11.2, together with the
explicit factors in (LC179), gives
$|\mathcal A'/\mathcal A(u)|\le CL$ there; its sector stays
a fixed distance from the negative real axis.

Choose a universal $a>0$ sufficiently small. The radius
$a|\eta|/L^2$ is at most $d/4$, by (LC180).
Integrate the logarithmic derivative of the nonzero function
$F(\Phi(u))=\mathcal A(u)\zeta(u)$ along segments in this disc.
Its modulus is at most $2|F(\Phi(s))|$ on the smaller chosen disc.
For $t=\Phi(s)$, $|t|\asymp Q^2$; the local square-root inverse
of $\Phi$ sends a $t$-disc of radius
$r_t=a_0T|\eta|/L^2$, with another fixed sufficiently small
$a_0>0$, into that chosen $s$-disc. Thus

$$
r_t=\frac{a_0T|\eta|}{L^2},\qquad
M_t(r_t)\le2|F(t)|,\qquad s\in\partial D.
\tag{LC184}
$$

This is a boundary-relative bound on the unchanged source. It is
not obtained by dividing an absolute Taylor error by an unproved
zero-free-strip lower bound.

### Pay every remote arc and dominate uniformly in height and distance

Insert (LC184) into the exact contour estimate (LC177).
Retain $G(|t|)\le\exp(CQL)$ from the previously used source-growth
supplier on the remote arc, and divide by the independent floor
(LC182). The factor $E_T^{-1}$ and the remote subtraction budget
$1+|t|/r_t$ are absorbed into the displayed exponent. Uniformly on
$\partial D$ this gives

$$
\frac{|\mathcal J_n(t)-F(t)|}{|F(t)|}
\le\frac{CQ^2L^4}{n|\eta|^2}
+C\sqrt n\exp\!\left[
-\frac{cn|\eta|^2}{Q^2L^4}+CQL+CK_\eta\log V_T\right].
\tag{LC185}
$$

Take one sufficiently large universal $C_*$ and set

$$
\mathcal N_*(T,\eta)
=\left\lceil C_*Q^3|\eta|^{-2}L^5B_\eta\right\rceil.
\tag{LC186}
$$

For $n\ge\mathcal N_*$ the first term of (LC185) is at most
$C/(C_*QLB_\eta)$. The remote factor
$\sqrt n\exp[-cn|\eta|^2/(Q^2L^4)]$ is decreasing once
$n\ge Q^2L^4/(2c|\eta|^2)$, which this same threshold meets.
At the threshold its negative exponent has size at least
$cC_*QLB_\eta$.
Its remaining logarithmic cost is at most

$$
CQL+CK_\eta\log V_T+\tfrac12\log(2C_*)
+\tfrac32L+\log(1/|\eta|)
+\tfrac52\log L+\tfrac12\log B_\eta+O(1).
$$

Since $K_\eta\log V_T=O(LB_\eta)$,
$\log B_\eta\le B_\eta$, and $Q\ge34$, one fixed increase of
$C_*$ dominates this cost for every allowed height and every distance,
including arbitrarily small $|\eta|$. Increasing it once more makes
the right side of (LC185) strictly below one for every integer
$n\ge\mathcal N_*$. No arc is deleted and no fixed-distance
asymptotic is substituted for this joint estimate.

### Same-source capture and its remaining obstruction

Apply Rouché on $D$ in the $s$ plane to
$\mathcal J_n(\Phi(s))$ and $F(\Phi(s))=\xi(s)/\xi_0$.
Their multiplicity counts there agree and are positive.
The map $\Phi$ is injective on this high disc and has nonzero
derivative, so these are actual zeros of the unchanged
$\mathcal J_n$, with multiplicity. Every $s\in D$ satisfies
$|\Re(s-1/2)|\ge15|\eta|/16$ and $\Im s>0$; hence
$\Im\Phi(s)=-2\Re(s-1/2)\Im s\ne0$.
Conjugation gives $\Delta_n\ge2$ for every $n\ge\mathcal N_*$.
The accepted exact defect ledger then yields

$$
b_\Delta\le\mathcal N_*(T,\eta)-1,
\qquad
\mathcal N_*(T,\eta)
=O\!\left((T+2)^3|\eta|^{-2}
          [\log(T+2)]^5[1+\log(1/|\eta|)]\right).
\tag{LC187}
$$

For $|\eta|\ge\eta_0>0$ this is a polynomial height bound.
For each fixed $A>0$ and $|\eta|\ge T^{-A}$ in the allowed
range it is $O_A(T^{3+2A}(\log T)^6)$.
The global bound (LC172) remains usable independently; the present
application pays a smaller joint degree by controlling the original
source locally relative to itself on a contour with chosen clearance.
Its classical source suppliers are reused; no originality assurance
is made for this quantitative application.

No source-zero spacing or simplicity hypothesis is required.
No numerical values of $C_Z,a_0,C_*$, new verified zero height or
finite-degree certificate are supplied. This is conditional source-zero
detection, not a reverse location theorem for all Jensen roots, a source
zero exclusion, or a root trajectory from the captured zero to the first
failed actual node. It asserts neither an integer collision nor
$t\asymp T^2$ for that real witness. Uniform actual-node strict
comparison below $T_n^{\rm mov}$, RH and strict Robin for every
$H>5040$ remain open. This is ordinary analysis without Lean
certification.

## Angular source payment and two-way local zero capture

Keep the original $F$, zero coefficient shift, exact moments (LC176),
local relative bound (LC184), and the checked Buck and Titchmarsh
suppliers of (LC180)--(LC183). The sectorial Gamma bound and the
functional equation are the same published DLMF inputs already used
in this note. No generic saddle, Gaussian, Cartan, zero-count or
logarithmic-derivative theorem is reproved. The following is an ordinary
source-specific application, with no Lean certification or originality
assurance.

The term $CQL$ in (LC185) pays the global source maximum over the
remote circle. Its sharper angular payment below keeps the same source
on the whole circle. This also lets the local comparison apply outside
the complete exceptional union, rather than only on a disc chosen
around a presumed source zero. The resulting reverse statement has
an explicit window and resolution; it is not a location theorem for
all complex Jensen roots.

### A full-circle envelope for the unchanged source

Let $T\ge32$, $Q=T+2$, $L=\log Q$ and $E_T=e^{-\pi T/4}$.
For $|s-(1/2+iT)|\le1$ put $w=-i(s-1/2)$ and $t=w^2=\Phi(s)$.
For $-\pi\le\theta\le\pi$, put
$u=we^{i\theta/2}$, $x=|\Im u|$, $y=|\Re u|$ and
$S=1/2+x+iy$.
The even entire identity $F(u^2)=\Xi(u)/\xi_0$, conjugation and the
functional equation give
$|F(te^{i\theta})|=|\xi(S)|/\xi_0$.
There is no global square-root branch in this identity.

Here $|w-T|\le1$ and
$|S|^2=|w|^2+x+1/4$, so $|S|=T+O(1)$ and $|S|<Q$.
The real part $\sigma=1/2+x$ can grow with $T$; replacing the
Gamma power's base by an unspecified comparable quantity would lose
uniform constants. Retain $|S|$ until the explicit upper base $Q$
is used.

The same sectorial Stirling bound gives
$|\Gamma(S/2)|\le C(|S|/2)^{\sigma/2-1/2}e^{-\pi y/4}$.
Indeed its angular factor is
$e^{-\sigma/2-\pi y/4+(y/2)\arctan(\sigma/y)}$, and
$y\arctan(\sigma/y)\le\sigma$, including the limit $y=0$.
The sector $|\arg(S/2)|\le\pi/2$ stays fixed.
When $1/2\le\sigma\le2$, one has $y=T+O(1)$, so reuse (LC134)
with summation length comparable to $T$ to bound $|\zeta(S)|\le C\sqrt Q$.
When $\sigma\ge2$, use the Dirichlet-series constant instead.
The explicit $S(S-1)\pi^{-S/2}$ factor then gives
$|F(te^{i\theta})|\le CQ^{9/4+x/2}e^{-\pi y/4}$.

Writing $w=a+ib$, one has
$x\le1+(T+1)|\theta|/2$ and
$T-y\le1+(T+1)\theta^2/8+|\theta|/2\le C+CQ|\theta|$.
Thus the original source on its entire circle satisfies

$$
|F(te^{i\theta})|
\le CE_TQ^4\exp(CQL|\theta|),
\qquad -\pi\le\theta\le\pi.
\tag{LC188}
$$

The Gamma attenuation is kept even on the remote arc; the positive
angular growth is explicitly bounded rather than deleted.

### A smaller all-distance threshold on the same source contour

First keep the source-zero premise and target disc from (LC181)--(LC182),
with $h=|\eta|$, $0<h<1/2$, and write
$K_h=6+\log(3072/h)/\log2$, $B_h=1+\log(1/h)$.
For a boundary point take the same $r_t=a_0Th/L^2$ as in (LC184),
and put $\theta_0=r_t/(2|t|)\asymp h/(QL^2)$.
Reuse the exact constant/linear subtraction and the local term in
(LC177). On its remote arc the fixed kernel satisfies
$|\mathcal K_n(\theta)|\le C\sqrt n e^{-c_0n\theta^2}$.
Equation (LC188), divided by the independently obtained floor
$cE_TV_T^{-K_h}$, bounds the unsubtracted source there by
$CQ^4V_T^{K_h}e^{CQL|\theta|}$.
The subtracted constant and derivative cost at most
$C(1+|t|/r_t)$ relative to $|F(t)|$, using (LC184) and Cauchy.

For $|\theta|\ge\theta_0$, the positive angular exponent is absorbed
into half the Gaussian exponent whenever

$$
n\ge C_0Q^2L^3/h.
\tag{LC189}
$$

Since $\log[Q^4+1+|t|/r_t]=O(L+\log(1/h)+\log L)$ is
bounded by $CK_h\log V_T$, the full remote integral and the
unchanged central term now give

$$
\frac{|\mathcal J_n(t)-F(t)|}{|F(t)|}
\le\frac{CQ^2L^4}{nh^2}
+C\sqrt n\exp\!\left[
-\frac{cnh^2}{Q^2L^4}+CK_h\log V_T\right],
\quad s\in\partial D,\quad n\text{ satisfying (LC189)}.
\tag{LC190}
$$

This uses the pre-maximum remote integral from (LC177), not a
replacement of its constant $G(|t|)$ by a variable inside a finished
inequality. The whole original circle and both subtraction terms
remain included.

Choose one sufficiently large universal $C_2$ and set

$$
\mathcal N_{\rm ang}(T,h)
=\left\lceil C_2Q^2h^{-2}L^5B_h\right\rceil.
\tag{LC191}
$$

This threshold meets (LC189) because its ratio to $Q^2L^3/h$ is
$C_2h^{-1}L^2B_h$. For every $n\ge\mathcal N_{\rm ang}$,
the central fraction is at most $C/(C_2LB_h)$.
The remote factor decreases once $n\ge Q^2L^4/(2ch^2)$,
also covered by the same choice of $C_2$.
At the threshold its negative exponent has magnitude at least
$cC_2LB_h$, while its remaining logarithmic cost is bounded by

$$
CK_h\log V_T+\tfrac12\log(2C_2)+L+\log(1/h)
+\tfrac52\log L+\tfrac12\log B_h+O(1).
$$

Use $K_h\log V_T=O(LB_h)$, $\log B_h\le B_h$, $Q\ge34$,
and $0<h<1/2$. One universal increase of $C_2$ makes (LC190)
strictly less than one for every allowed height, resolution and degree.
This is uniform for arbitrarily small $h$, not a fixed-distance limit.

The already established Rouché and defect-ledger application
(LC187), using this smaller threshold, therefore gives conditionally
on the same actual off-line source zero

$$
b_\Delta\le\mathcal N_{\rm ang}(T,|\eta|)-1,
\qquad
\Delta_n\ge2\quad(n\ge\mathcal N_{\rm ang}(T,|\eta|)).
\tag{LC192}
$$

For fixed $A>0$ and $|\eta|\ge T^{-A}$ this sufficient degree is
$O_A(T^{2+2A}(\log T)^6)$.
The earlier thresholds (LC168) and (LC186) remain valid independently;
no previous assumption or source is changed.

### Extend the comparison outside the complete union

For a two-way local statement remove the premise that a source zero
is already present. Let $h\in(0,1/2)$ be a requested resolution and
let $m_T$ count the actual nontrivial zeros with
$|\Im\rho'-T|\le2$, with multiplicity. The same Euler anchor and
reciprocal pole-count inequality in (LC180) give $m_T=O(L)$,
including $m_T=0$.
Set

$$
M_T=\max(1,m_T),\qquad d=h/(64M_T).
\tag{LC193}
$$

Take Buck's complete exceptional union at scale $2$ and
$\epsilon=h/3072$, add radius-$d$ discs about each distinct counted
zero, and merge the complete union. Call it $U$ in the $s$ plane.
Its total radii are at most $h/32$, also when the count is zero.
For every $s\notin U$ with $|s-(1/2+iT)|\le3/4$, the same independently
obtained Gamma/Buck floor and chosen clearance hold:

$$
|F(\Phi(s))|\ge cE_TV_T^{-K_h},\qquad
\operatorname{dist}(s,\{\rho':|\Im\rho'-T|\le2\})\ge d
\quad\text{if this set is nonempty}.
\tag{LC194}
$$

On the $d/4$ neighborhood, every zero in Titchmarsh's local sum
is still in this counted window: $3/4+d/4+1<2$. If $m_T=0$ its sum is empty and
$|\zeta'/\zeta|=O(L)$. Otherwise use the same clearance estimate.
In both cases $|\mathcal A'/\mathcal A+\zeta'/\zeta|\le CL^2/h$,
and a fixed sufficiently small radius $ah/L^2$ is at most $d/4$.
The local inverse and relative modulus argument of (LC184) applies
unchanged. Equations (LC188)--(LC191) consequently give the strict
relative error throughout this complement, with one universal constant
chosen to cover both counts. The absence of a presumed target zero
has not removed the independent floor.

### Both functions' local zeros lie in the same small clusters

Define the closed windows

$$
\begin{aligned}
W(T,h)&=\{s:|s-(1/2+iT)|\le1/2,\ |\Re(s-1/2)|\ge h\},\\
W^+(T,h)&=\{s:|s-(1/2+iT)|\le1/2+h/16,\
                         |\Re(s-1/2)|\ge15h/16\}.
\end{aligned}
\tag{LC195}
$$

Select every merged disc in $U$ that meets $W(T,h)$; this choice is
independent of $n$. Its radius is at most $h/32$, so its closure is
within $h/16$ of any one intersection point. It lies in $W^+(T,h)$,
inside the radius-one window, and avoids the critical line.
Its entire boundary is outside $U$ and satisfies the strict comparison.
Rouché gives equal zero counts of $\xi(s)/\xi_0$ and
$\mathcal J_n(\Phi(s))$ on each selected disc for every
$n\ge\mathcal N_{\rm ang}(T,h)$.
No selected disc is required to contain a source zero beforehand.
If it contains a polynomial zero, the equal positive count supplies
an actual source zero there. In particular this also handles an
empty local source count.

Let $\nu_f(E)$ count zeros of $f$ with multiplicity. Every source zero
in $W$ belongs to $U$ by the floor; every polynomial zero there
belongs to $U$ by the strict error in its complement. Summing the
equal counts on the disjoint selected discs yields

$$
\begin{aligned}
\nu_{\mathcal J_n\circ\Phi}(W(T,h))
 &\le\nu_\xi(W^+(T,h)),\\
\nu_\xi(W(T,h))
 &\le\nu_{\mathcal J_n\circ\Phi}(W^+(T,h)),
\qquad n\ge\mathcal N_{\rm ang}(T,h).
\end{aligned}
\tag{LC196}
$$

More precisely each polynomial zero in $W$ shares its selected disc
with a source zero at distance at most $h/16$, and conversely.
These are multiplicity-preserving cluster counts, not a unique matching
or a source-zero spacing statement. The high window makes $\Phi$
injective with nonzero derivative, and its off-line discs have nonreal
images. Thus they are actual original-$\mathcal J_n$ roots, not zeros
of a changed source or only of a leading approximation.

In particular, a separately certified absence of source zeros in $W^+$
excludes polynomial zeros in $W$ for every degree meeting (LC191).
It does not certify a numerical degree until the universal constants
are instantiated. No existing verified zero-height range is extended.

### How far this approaches the unpaid actual-node interval

For each fixed $h>0$ in the allowed range,
$T_n\to\infty$ with
$T_n=o(\sqrt n/(\log n)^{5/2})$ eventually meets (LC191).
For $h_n=T_n^{-A}$, fixed $A>0$, the sufficient relation is

$$
T_n^{2+2A}(\log T_n)^6=o(n).
\tag{LC197}
$$

Thus there is two-way localization in specified growing windows,
including their source and polynomial multiplicities. It still controls
no arbitrarily thin band without its explicitly growing resolution cost.
For fixed resolution its squared-frequency scale is
$t=o(n/(\log n)^5)$, whereas the unpaid actual-node interval extends
to $T_n^{\rm mov}\asymp n/\log n$. Those scales cannot be identified.

To use (LC196) at a first defect birth, one would have to locate a
nonreal zero of $\mathcal J_{b_\Delta+1}$ in a covered window with
$b_\Delta+1\ge\mathcal N_{\rm ang}(T,h)$.
The real-node witness (LC165) supplies neither this complex-root
location nor its off-line distance $h$. At a real node the source
floor can vanish, so the present strict relative error cannot be
substituted for $\mathcal J_n'(t)\mathcal G_n(t)>0$.
Growing real-cluster signed margins, the larger-height and thinner-band
complex-root exclusions, initial-degree overlap, RH and strict Robin
for every integer $H>5040$ remain open. This source application has
no Lean or numerical-constant certificate and no originality claim.


### Reuse the verified-height lower bound at the first source height

The known finite-degree implication (VH) is already recorded in
[the Jensen supplier](../Zeros/osullivan2021modifiedjensen.md#known-finite-degree-coverage-from-verified-zero-height).
Its primary source is Griffin, Ono, Rolen, Thorner, Tripp and Wagner,
[*Jensen polynomials for the Riemann xi-function*, arXiv:1910.01227v3](https://arxiv.org/abs/1910.01227v3),
Theorem 1.2 at $m=0$, which the authors identify as Chasse's
Theorem 1.8. Reuse that theorem, without another sector or
real-root-preserver proof. Their coefficient convention (1.1)--(1.2)
and $a_k=\Gamma_k/(\xi_0 k!)$ give exactly
$\mathcal J_n(t)=\xi_0^{-1}J^{n,0}(-t/n)$.
Thus their degree is this note's $n$, and their coefficient shift is zero.

Conditionally on an actual off-line source zero, let $T_0\ge32$
be the least positive ordinate of any such zero and choose one of
its zeros $1/2-\eta_0+iT_0$, $0<|\eta_0|<1/2$.
This minimum exists: source zeros are discrete, a bounded-height
closed critical strip contains finitely many, and conjugation supplies
a positive ordinate. The source has no real zero in the critical strip.
Let $D=b_\Delta+1$ be the first nonhyperbolic zero-shift degree;
(LC192) supplies its finiteness. For every $T<T_0$, the premise
$\mathrm{RH}_0(T)$ of (VH) holds. Take $T$ sufficiently close to $T_0$
from below that $\lfloor T\rfloor=\lceil T_0\rceil-1$.
The already proved finite-degree implication and (LC192) then bracket
that first degree:

$$
(\lceil T_0\rceil-1)^2<D=b_\Delta+1
\le\mathcal N_{\rm ang}(T_0,|\eta_0|).
\tag{LC198}
$$

The lower inequality is the published (VH) applied to the unchanged
source; only its pairing with the angular upper bound is made here.
It cannot be attached to an arbitrary later off-line zero. Equivalently,
a nonhyperbolic degree $D$ forces an off-line source zero of height at
most $\lceil\sqrt D\rceil$, by the contrapositive of (VH).
These degree--height implications still give neither the location nor
the distance from the critical line of a particular nonreal polynomial
root. They do not meet the first-birth window and resolution obligation
following (LC197).

### A published adjacent-row interface, without a new sign estimate

A further reusable supplier is Alexandre Dumas,
[*Adjacent-Shift Proper Position for Jensen Polynomials*, Zenodo v1.1](https://doi.org/10.5281/zenodo.22897068),
Theorem 2.3, a preprint. Its published hyperbolicity--proper-position
interface is used here only with its original positive-sequence
hypotheses; it is not a new structural theorem or a Lean result.
Put $c_k=k!a_k=\Gamma_k/\xi_0>0$ and use the supplier's notation
$J_c^{d,m}(x)=\sum_{k=0}^d\binom dk c_{m+k}x^k$.
For $P_n=J_c^{n,0}$, $Q_n=J_c^{n,1}$ and $R_n=J_c^{n+1,0}$,
the parameter map is exactly

$$
P_n(-t/n)=\mathcal J_n(t),\qquad
Q_n(-t/n)=-\mathcal G_n(t),\qquad
R_n=P_n+xQ_n.
$$

With the supplier's oriented Wronskian $W[P,Q]=P'Q-PQ'$, this gives

$$
W[P_n,Q_n](-t/n)
=n\bigl(\mathcal J_n'(t)\mathcal G_n(t)
       -\mathcal J_n(t)\mathcal G_n'(t)\bigr).
$$

Theorem 2.3 states that $R_n$ is hyperbolic if and only if $P_n,Q_n$
are hyperbolic and $W[P_n,Q_n]\ge0$ on the entire real axis.
If $R_n$ has $n+1$ distinct real roots, its strict version gives
$\mathcal J_n'(t)\mathcal G_n(t)>0$ at every actual positive
$\mathcal J_n$ node. With only hyperbolicity, it supplies a weak sign;
repeated roots and common zeros cannot be discarded. The verified-height
input therefore already gives this weak actual-node sign when
$n+1\le9\cdot10^{24}$, without adding an all-degree statement.
Source-zero simplicity is not a certificate of Jensen-root simplicity.

The supplier's Theorem 5.1 expresses the global Wronskian sign as a
positive-semidefinite Gram representation, assuming both rows are
hyperbolic. Neither that equivalence nor the adjacent-shift transfer
constructs the required Gram matrices for all zero-shift degrees.
A strict source-specific joint margin in the unpaid moving real band
remains the missing estimate. Reusing this interface changes its
formulation, without reducing that gap or proving RH or strict Robin.


## A polynomial cluster model without a prescribed source-root spacing

The fixed-cluster conditions (LC27) use a pure-multiplicity Hermite
model. For a cluster of close distinct real zeros, a finite polynomial
model has a reusable separation supplier: Katkova, Shapiro and
Vishnyakova, [*Multiplier sequences and logarithmic mesh*,
arXiv:1010.6052v1](https://arxiv.org/abs/1010.6052v1), Theorem 6,
printed p.3; the published DOI is
[10.1016/j.crma.2010.11.031](https://doi.org/10.1016/j.crma.2010.11.031).
Their theorem bounds the logarithmic mesh of a Schur--Szego product
below by the larger input mesh. It permits repeated input roots.
Reuse that theorem and the existing finite Laguerre and adjacent-row
identities, without another general multiplier or root-repulsion proof.
The bounds below are ordinary model applications, without Lean or
originality certification. They do not yet estimate the original
source's growing real-cluster error.

### The finite Jensen model acquires its own separation

For a polynomial $q(t)=\sum q_kt^k$ define
$\mathscr T_nq(t)=\sum_{k=0}^n(n)_{\underline k}n^{-k}q_kt^k$.
Let $Q(t)=\prod_{j=1}^r(t-\tau_j)$, where $2\le r\le n$ and
$\tau_j\ge\tau_{\min}>0$; repetitions are allowed. Put
$H=\mathscr T_nQ$ and $V=\mathscr T_nQ'$.
The diagonal symbol in degree $r$ is

$$
B_{r,m}(u)=\sum_{k=0}^r\binom rk\frac{(m)_{\underline k}}{m^k}u^k
=r!(u/m)^rL_r^{(m-r)}(-m/u),\qquad m\ge r.
\tag{LC199}
$$

This is exactly [DLMF (18.5.12)](https://dlmf.nist.gov/18.5.E12)
in the stated parameters, with its polynomial continuation at $u=0$.
The Laguerre polynomial has positive simple roots
$\ell_1<\cdots<\ell_r$, because $m-r\ge0$; reuse the classical
orthogonal-polynomial zero theorem in
[DLMF section 18.2(vi)](https://dlmf.nist.gov/18.2#vi).
Thus $B_{r,m}$ has simple negative roots $-m/\ell_j$ and mesh
$\zeta_{r,m}=\min_{j<r}\ell_{j+1}/\ell_j>1$.

The Schur--Szego product of $Q(-u)$ and $B_{r,n}(u)$ is exactly
$H(-u)$ in the binomial coefficient convention. Both inputs have only
negative roots. Theorem 6 therefore gives
$\operatorname{lmesh}(H)\ge\zeta_{r,n}>1$.
In particular $H$ has positive simple roots, even if some or all
$\tau_j$ coincide. This is a consequence of the published theorem,
not a source-root spacing hypothesis. No large-$n$, fixed-$r$ limit
has been used. The same observation applies with ambient degree $n+1$.

### An explicit joint model margin

Use only the polynomial identity accompanying Dumas's Theorem 2.3
in the cited [adjacent-row supplier](https://doi.org/10.5281/zenodo.22897068).
Its finite coefficient identities remain valid when the coefficients
above index $r$ vanish; its positive-sequence equivalence is not applied
to that zero tail. Set

$$
\begin{aligned}
P(x)&=\sum_{k=0}^r(n)_{\underline k}(-1)^kq_kx^k,\\
Q_1(x)&=\sum_{k=0}^{r-1}(n)_{\underline k}(k+1)(-1)^{k+1}q_{k+1}x^k,\\
R(x)&=\sum_{k=0}^r(n+1)_{\underline k}(-1)^kq_kx^k.
\end{aligned}
$$

Here $q_k$ are the coefficients of the monic $Q$, not coefficients
of a changed original source. One has $R=P+xQ_1$,
$R'=(n+1)Q_1$, $P(-t/n)=H(t)$ and $Q_1(-t/n)=-V(t)$.
The reused Wronskian identity is
$W[P,Q_1]=[n(R')^2-(n+1)RR'']/(n+1)^2$.
The polynomial $R$ has $r$ simple negative roots. For its minimum
root magnitude reuse another already cited result:
Arizmendi, Fujie, Perales and Ueda,
[*S-transform in finite free probability*, arXiv:2408.09337v2](https://arxiv.org/html/2408.09337v2),
Introduction following (1.2), recalls the classical bound
$\max\operatorname{root}(p\boxtimes_rk)\le
(\max\operatorname{root}p)(\max\operatorname{root}k)$
for polynomials with nonnegative roots. Put
$p(y)=y^rQ(1/y)/Q(0)$ and
$k(y)=(-1)^rr!L_r^{(n+1-r)}(y)$.
Their normalized elementary coefficients are respectively those of
the reciprocal source-cluster roots and $(n+1)_{\underline j}$.
Coefficient matching in (1.1)--(1.2) gives exactly
$y^rR(-1/y)/R(0)=p\boxtimes_rk$.
If $\ell_{r,n+1}$ is the largest root of that Laguerre polynomial,
the cited product bound therefore gives
$|r_j|\ge\tau_{\min}/\ell_{r,n+1}$ for every root of $R$.
Consequently its absolute root gaps are at least

$$
\begin{aligned}
\delta_{r,n}&=(\zeta_{r,n+1}-1)\frac{\tau_{\min}}{\ell_{r,n+1}},\\
f_r&=\lfloor(r-1)/2\rfloor!\,\lceil(r-1)/2\rceil!,\\
\mu_{r,n}&=\frac{n+1-r}{n(n+1)^2}
             ((n+1)_{\underline r})^2
             (\delta_{r,n}/2)^{2r-2}f_r^2>0.
\end{aligned}
\tag{LC200}
$$

For real $x$ away from the roots of $R$, the same real-root expansion
used in the supplier gives
$W[P,Q_1]=R^2[(n+1)\sum_j(x-r_j)^{-2}
-(\sum_j(x-r_j)^{-1})^2]/(n+1)^2$.
Cauchy--Schwarz bounds this below by
$(n+1-r)/(n+1)^2\sum_j(R/(x-r_j))^2$.
Choose a nearest root $r_j$. For $k\ne j$,
$|x-r_k|\ge|r_j-r_k|/2\ge|j-k|\delta_{r,n}/2$.
Since the absolute leading coefficient of $R$ is
$(n+1)_{\underline r}$, that single summand supplies the square
in (LC200), with $(j-1)!(r-j)!\ge f_r$.
Polynomial continuity covers the root points as well.
The exact parameter map then gives the global real-variable model bound

$$
H'(t)V(t)-H(t)V'(t)\ge\mu_{r,n}\qquad(t\in\mathbb R).
\tag{LC201}
$$

The Laguerre root sum is $r(n+1)$, so
$\ell_{r,n+1}\le r(n+1)$. Compared with using only $R$'s own
reciprocal-root sum, the model margin is improved by the explicit
factor $[r(n+1)/\ell_{r,n+1}]^{2r-2}$.
Every dependence on $r,n$ and the Laguerre mesh remains in (LC200).
In particular a positive margin for each finite model is not an
$r$-uniform constant or a bound on the actual source's errors.

### Keep the source factor's drift in the model

For real $a_*\ne0$, $b$ and center $\tau$, consider the auxiliary
entire function $f_*(z)=a_*e^{b(z-\tau)}Q(z)$.
Finite coefficient extraction, with the same ambient $n$, gives exactly

$$
\begin{aligned}
d(t)&=1+bt/n,\quad y(t)=t/d(t),\quad E(t)=a_*e^{-b\tau}d(t)^n,\\
M(t)&=\mathscr T_nf_*(t)=E(t)H(y(t)),\\
U(t)&=\mathscr T_nf_*'(t)=E(t)\{V(y(t))+bH(y(t))\},\\
M'(t)U(t)-M(t)U'(t)
&=a_*^2e^{-2b\tau}d(t)^{2n-2}
   \{H'(y(t))V(y(t))-H(y(t))V'(y(t))\}.
\end{aligned}
\tag{LC202}
$$

These are the ordinary exponential tilt and its transported derivative;
the extra $bH$ term is retained. On a prescribed compact interval $I$
where $d(t)>0$, define
$\mu_*(I)=a_*^2e^{-2b\tau}\min_{t\in I}d(t)^{2n-2}\mu_{r,n}>0$.
Equation (LC201) then supplies the same lower bound for the model
Wronskian on all of $I$. The pole of the displayed fractional coordinate
is excluded explicitly; the extracted polynomials themselves still
have their polynomial continuation there.

In a selected real source cluster with $F=AQ$ and $A$ zero-free near
$\tau$, one can choose $a_*=A(\tau)$ and $b=A'(\tau)/A(\tau)$.
Reality makes these real and $a_*\ne0$. This does not assume that $A$
is constant or that the source has only real zeros elsewhere. The
auxiliary $f_*$ is a comparison function; $F$, $\mathcal J_n$,
$\mathcal G_n$ and coefficient shift zero remain unchanged.

### The unpaid part is now a four-response source budget

On the same independently prescribed $I$, write

$$
\begin{aligned}
e_0&=\|\mathcal J_n-M\|_I,&
e_1&=\|\mathcal J_n'-M'\|_I,\\
v_0&=\|\mathcal G_n-U\|_I,&
v_1&=\|\mathcal G_n'-U'\|_I,
\end{aligned}
$$

where $\|\cdot\|_I$ is the uniform norm. Set
$S_0=\|M\|_I$, $S_1=\|M'\|_I$, $T_0=\|U\|_I$, $T_1=\|U'\|_I$.
Expanding the two products at the same argument gives the sufficient
joint condition

$$
e_1T_0+S_1v_0+e_1v_0+e_0T_1+S_0v_1+e_0v_1
<\mu_*(I).
\tag{LC203}
$$

Under (LC203), $\mathcal J_n'\mathcal G_n-
\mathcal J_n\mathcal G_n'>0$ on $I$. At every actual
$\mathcal J_n$ node in $I$, this is the required strict product
$\mathcal J_n'\mathcal G_n>0$. No approximate-node replacement,
source-zero simplicity or within-cluster spacing is needed for this
implication. It also excludes repeated or adjacent-common actual
nodes in the certified interval. Condition (LC203) is stronger than
positivity only at nodes; its failure is not a counterexample to that
target.

No bound proving (LC203) for the actual growing source clusters is
supplied here. The four errors are exact transforms of $F-f_*$ and its
derivatives; their local and remote contributions, including the
$n-1$ extraction offsets, must be paid on the original source contour.
The real-cluster premise must also be checked for every cluster being
used. A positive model margin cannot turn a cluster containing
nonreal source zeros into an all-real one. Neither the isolated-cluster
geometry nor the required growing-$r$ error bound is supplied by the
five FIB inclusion modes, reference-frame rotation or an unweighted
length-conservation identity. RH and strict Robin for every integer
$H>5040$, all-node coverage and a numerical margin certificate remain
unresolved; this model application has not been checked in Lean.




### A local original-source bound after removing the selected real zeros

The model factor can receive a source-specific local estimate through
Titchmarsh's already checked Theorem 9.6(A), rather than an assumed
pointwise lower bound on $F'$ at a multiple source zero.
Let $T\ge32$, $L=\log(T+2)$, $s_0=1/2+iT$ and $0<\rho\le1/8$.
Assume that all source zeros in the closed disc $|s-s_0|\le4\rho$
lie on the critical line; this is a selected local premise, not RH.
List those zeros as $1/2+i\gamma_j$, with multiplicities, and form
$Q(z)=\prod_j(z-\gamma_j^2)$.
For use with the preceding model assume its degree is at least two.
The existing count in (LC193) bounds its degree by $CL$.
Put $\tau=T^2$ and $A(z)=F(z)/Q(z)$.
The removed multiplicities are exactly those of $F$ because $\Phi$
is injective and noncritical near $s_0$. Thus $A$ is analytic and
zero-free on the image of the open radius-$4\rho$ disc.
No condition is imposed on the other source zeros.

Let $\Sigma_T$ contain every source zero $\omega$ with
$|\Im\omega-T|\le2$, with multiplicity. On $|s-s_0|\le1/2$,
Titchmarsh's local sum is a subset of $\Sigma_T$.
The extra terms each have $|\Im\omega-\Im s|>1$, so replacing that
varying sum by the fixed one changes the bound by $O(L)$.
The already used Gamma/polynomial factor for $\xi$ also has logarithmic
derivative $O(L)$ there. The remainder after this fixed pole sum is
analytic near the selected disc and is uniformly $O(L)$.

For each selected zero,
$\Phi(s)-\gamma_j^2=-(s-1/2-i\gamma_j)(s-1/2+i\gamma_j)$.
Hence its near pole cancels in
$g(s)=\frac{d}{ds}\log A(\Phi(s))$.
Its conjugate pole is at distance comparable to $T$ and costs at most
$Cr/T$ in total. All remaining poles in $\Sigma_T$ are outside the
radius-$4\rho$ disc, so on the radius-$2\rho$ disc they are at least
$2\rho$ away. The fixed count and Cauchy estimate consequently give

$$
|g(s)|\le CL/\rho\quad(|s-s_0|\le2\rho),\qquad
|g'(s)|\le CL/\rho^2\quad(|s-s_0|\le\rho).
\tag{LC204}
$$

These bounds hold across the removed source zeros. They require no
separation between those zeros and no simplicity assumption.
Cauchy is applied to the analytic pole-removed function $g$, not to
$F'/F$ across its poles or to a discontinuously selected zero sum.

The local inverse of $\Phi(s)=-(s-1/2)^2$ maps
$|z-\tau|\le T\rho/4$ inside $|s-s_0|<\rho/2$; its first and second
derivatives are bounded by $C/T$ and $C/T^3$.
Applying the chain rule to (LC204) gives
$|(\log A)'|\le CL/(T\rho)$ and
$|(\log A)''|\le CL/(T^2\rho^2)$ on that $z$ disc.
Choose $a_*=A(\tau)\ne0$ and $b=A'(\tau)/A(\tau)$ as in (LC202).
An analytic logarithm of $A(z)/A(\tau)$ exists on this disc, with
value zero at $\tau$. Its linear Taylor remainder therefore gives

$$
\begin{aligned}
|b|&\le CL/(T\rho),\\
\left|\frac{A(z)}{a_*e^{b(z-\tau)}}-1\right|
&\le\exp\!\left(\frac{CL|z-\tau|^2}{T^2\rho^2}\right)-1,\\
|F(z)-f_*(z)|
&\le |f_*(z)|\left\{
\exp\!\left(\frac{CL|z-\tau|^2}{T^2\rho^2}\right)-1\right\},
\qquad |z-\tau|\le T\rho/4.
\end{aligned}
\tag{LC205}
$$

The last line is also valid at zeros of $Q$ by continuity; it divides
only by the zero-free factor, not by $F$. Reality of $F,Q$ gives real
$a_*,b$, even when the center itself is a removed source zero.
This is an original-source parameter application of the existing pole
sum, Gamma bounds, count and analytic Taylor estimate, without a new
local logarithmic-derivative theorem or Lean certification.

Equation (LC205) supplies a local curvature remainder for the model
factor. It does not supply the four extracted error bounds in (LC203):
those still involve the exact coefficient kernel, the derivative
extractions and the entire remote source circle. The interval and
cluster spread must also be small enough for a useful quadratic
remainder; the displayed exponential is not automatically small on
the whole disc. A uniform real-cluster premise, sufficient bounds
through the unpaid moving real-node band, numerical constants, RH and
strict Robin for every integer $H>5040$ remain unresolved.


### Extract all four errors from the same undifferentiated source remainder

The local factor estimate can be connected to the four-response budget
without separately supplying global bounds for $F'$ and $F''$.
This uses the existing exact coefficient circle (LC176); it is a
source-specific extraction interface, not another multiplier, mesh or
logarithmic-derivative theorem. The ordinary derivation below carries
no Lean or originality certificate and does not establish that the
resulting budget is small enough.

Keep the cluster, $Q$, $a_*,b,f_*$ and compact interval $I$ from
(LC202)--(LC205). Put $\mathscr D=F-f_*$, an entire function.
For $t>0$, $v=e^{i\theta}$, use exactly the kernel $\mathcal K_n$ in
(LC176) and define

$$
\begin{aligned}
\omega_0(t,\theta)&=1,\\
\omega_D(t,\theta)&=\frac nt(1-v),\\
\omega_G(t,\theta)&=\frac{(n+1)v^{-1}-n}{t},\\
\omega_{DG}(t,\theta)&=
\frac n{t^2}\{(n+1)v^{-1}+nv-2n\}.
\end{aligned}
\tag{LC206}
$$

The four actual errors, including both derivatives, are exactly

$$
\begin{pmatrix}
\mathcal J_n(t)-M(t)\\
\mathcal J_n'(t)-M'(t)\\
\mathcal G_n(t)-U(t)\\
\mathcal G_n'(t)-U'(t)
\end{pmatrix}
=
\int_{-\pi}^{\pi}\mathcal K_n(\theta)
\begin{pmatrix}\omega_0\\\omega_D\\\omega_G\\\omega_{DG}\end{pmatrix}
\mathscr D(te^{i\theta})\,d\theta.
\tag{LC207}
$$

For the derivative extraction differentiate the original circle and
integrate by parts, using
$\partial_\theta\mathscr D(tv)=itv\mathscr D'(tv)$ and
$\mathcal K_n'/\mathcal K_n=in(v-1)$.
Periodicity removes the endpoint terms. This gives $\omega_D$.
For $\mathscr T_n\mathscr D'$ the same integration by parts with the
additional $v^{-1}$ gives $\omega_G$.
Differentiating its integral in $t$ gives
$t^{-2}\{-A+i(\mathcal K_n A)'/\mathcal K_n\}$,
where $A=(n+1)v^{-1}-n$, which is exactly $\omega_{DG}$.
All integrands are smooth on the compact circle, so the differentiations
and integration by parts are legitimate. These identities keep the
$n-1$ and upper-adjacent extraction costs inside their exact weights;
in particular the $n+1$ terms cannot be replaced by $n$.
For $-\pi\le\theta\le\pi$ the weights satisfy

$$
|\omega_D|\le n|\theta|/t,\qquad
|\omega_G|\le\{1+(n+1)|\theta|\}/t,\qquad
|\omega_{DG}|\le n\{1+n\theta^2\}/t^2.
$$

The last bound uses the exact expression
$\omega_{DG}=n\{v^{-1}-2n(1-\cos\theta)\}/t^2$,
rather than discarding its opposite angular terms.

### One local--remote envelope for that source remainder

For the original-source specialization in (LC204)--(LC205), let
$R=T\rho/4$ and prescribe a nonempty compact
$I\subset(\tau-R,\tau+R)$, still with $d(t)>0$.
Set $t_{\max}=\max I$ and $a_I=\max_{t\in I}|t-\tau|<R$.
Choose
$0<\theta_0\le\min\{1,(R-a_I)/(2t_{\max})\}$.
Then every local-arc point $te^{i\theta}$, $t\in I$,
$|\theta|\le\theta_0$, lies in the disc covered by (LC205).
Write $\kappa_A=CL/(T^2\rho^2)$ with the same sufficiently large
source constant as that estimate. For $z=te^{i\theta}$ define

$$
\begin{aligned}
B_*(t,\theta)&=|a_*|e^{b(t\cos\theta-\tau)}
                     \prod_{j=1}^r|te^{i\theta}-\tau_j|,\\
B_F(t,\theta)&=CE_T(T+2)^4e^{C(T+2)L|\theta|},\\
\mathcal E_j&=\sup_{t\in I}\left\{
\int_{|\theta|\le\theta_0}|\mathcal K_n\omega_j|
 B_*(t,\theta)(e^{\kappa_A|te^{i\theta}-\tau|^2}-1)\,d\theta
+\int_{|\theta|>\theta_0}|\mathcal K_n\omega_j|
 \{B_F(t,\theta)+B_*(t,\theta)\}\,d\theta
\right\},\qquad j\in\{0,D,G,DG\}.
\end{aligned}
\tag{LC208}
$$

Here $B_*$ is the exact model modulus, retaining its signed drift
and all cluster roots. The already checked (LC188) supplies $B_F$:
$|t-\tau|<T\rho/4$ puts $1/2+i\sqrt t$ in its fixed source window.
On the local arc apply (LC205); on the remote arc use
$|\mathscr D|\le|F|+|f_*|$. Equation (LC207) then gives
$e_0\le\mathcal E_0$, $e_1\le\mathcal E_D$,
$v_0\le\mathcal E_G$ and $v_1\le\mathcal E_{DG}$ on the same $I$.
If numerical or symbolic evaluation is needed, the elementary bound
$|te^{i\theta}-\tau_j|\le|t-\tau_j|+t|\theta|$ keeps each
spread contribution explicit, without an input-spacing denominator.

Consequently, substituting these four upper bounds for the four errors
in (LC203) is a sufficient original-source contour criterion. Its
satisfaction would certify every actual node in this prescribed
interval. Both the original source and the model remain in every
remote integral; no source derivatives, independent-row approximations
or uncharged offset replacements enter this criterion.

The integrals are upper bounds, not a proved winning budget. No
height-uniform inequality comparing them with $\mu_*(I)$ is established.
The smallness of the local exponent, Gaussian suppression of the
remote model as well as source, growth of $r$, decline of the model
margin, placement of $I$, the local all-real-source premise and
all-node coverage must still be controlled jointly. Separate
localization or boundary relative-error bounds do not supply that
comparison. RH and strict Robin for every integer $H>5040$ remain
unresolved.


## A centred source-to-node budget in a growing real-source chart

A tangent fixed at the cluster center can leave an error proportional
to the square of the cluster spread even as the extraction degree grows.
For the actual-node sign task, the full-interval Wronskian certificate
(LC203) is sufficient but stronger than necessary. Instead freeze a
separate source tangent at each local model node, estimate against its
actual derivative product, and use only the three responses needed to
preserve endpoint signs and the two node factors. The original $F$,
$\mathcal J_n$, $\mathcal G_n$ and coefficient shift remain unchanged.

The suppliers below are reused: the finite-free root order theorem,
KSV's finite multiplier and mesh theorems, classical Laguerre equations,
the original exact circle, and the checked Buck/Titchmarsh source
estimates. This is an ordinary analytical application without Lean,
numerical-constant or originality certification. The local all-real
source premise remains explicit. It is not asserted for every height.

### Rootwise bounds retain the source cluster's spread

Let $H=\mathscr T_nQ$, $V=\mathscr T_nQ'$, where
$Q(z)=\prod_{j=1}^r(z-\alpha_j)$ has positive roots listed in
nondecreasing order, including repetitions. For $r\ge2$, write
$0<\beta_1<\cdots<\beta_r$ for the roots of $H$ and
$\kappa=(n)_{\underline r}/n^r$ for its leading coefficient.
The already cited Arizmendi--Fujie--Perales--Ueda,
[*S-transform in finite free probability*, arXiv:2408.09337v2](https://arxiv.org/html/2408.09337v2),
Notation 4.3 and Theorem 4.4, preserve the coordinatewise sorted-root
order under finite-free multiplicative convolution with a
nonnegative-root polynomial. This includes repeated input roots.
Reuse that theorem, rather than another root-monotonicity proof.

Put $S_{n,r}(z)=\mathscr T_n(z-1)^r$ and let $s_-,s_+$ be its
smallest and largest roots. In the supplier's monic convention,
$H/\kappa=Q\boxtimes_r(S_{n,r}/\kappa)$: its normalized elementary
coefficient of index $j$ is multiplied by
$\lambda_{n,r-j}/\kappa$.
Compare $S_{n,r}/\kappa$ with $(z-s_-)^r$ and $(z-s_+)^r$.
The two endpoint convolutions are dilations of $Q$, so the cited
order theorem gives the individual, rather than only extreme, bounds

$$
s_-\alpha_i\le\beta_i\le s_+\alpha_i.
\tag{LC209}
$$

For the source chart below, $\tau/2\le\alpha_i\le2\tau$.
When $n\ge25r$, the existing Laguerre symbol and classical zero
estimates give absolute constants $c,C>0$ such that, with
$\sigma=\tau/\sqrt n$,

$$
\max_i|\beta_i-\alpha_i|\le C\sigma\sqrt r,
\qquad
\delta:=\min_i(\beta_{i+1}-\beta_i)\ge c\sigma/\sqrt r,
\qquad
\kappa\ge e^{-Cr}.
\tag{LC210}
$$

Here is the precise Laguerre parameter application behind these costs.
The roots of $S_{n,r}$ are $n/x_j$, in reverse order, where $x_j$
are the roots of $L_r^{(n-r)}$.
The classical three-term recurrence from
[DLMF 18.9.13--14](https://dlmf.nist.gov/18.9#E13) gives the symmetric Jacobi matrix
with diagonal $n-r+2k-1$ and off-diagonal
$\sqrt{k(n-r+k)}$. Thus
$x_j\in[n-d,n+d]$ with
$d=r-1+2\sqrt{(r-1)(n-1)}<n/2$.
For the spacing, the Laguerre equation in
[DLMF Table 18.8.1, row 8](https://dlmf.nist.gov/18.8#T1), under its
usual removal of the first derivative, gives
$Y''+WY=0$ with
$W=-1/4+(n+r+1)/(2x)-((n-r)^2-1)/(4x^2)$.
Its positive supremum is
$\{(n+r+1)^2-(n-r)^2+1\}/\{4((n-r)^2-1)\}$.
The classical Dirichlet--Wirtinger inequality between consecutive
zeros therefore gives
$x_{j+1}-x_j\ge2\pi\sqrt{((n-r)^2-1)/((n+r+1)^2-(n-r)^2+1)}
\ge c\sqrt{n/r}$.
Combining these standard estimates with (LC209) and the already reused
KSV logarithmic-mesh bound proves (LC210). No source spacing enters.
The bound on $\kappa$ is the elementary logarithm of its finite product.
These are parameter applications, not new general Laguerre or
root-order theorems.

The same finite multiplier preserves the real-root pencils
$Q+uQ/(z-\alpha_\ell)$ for every real $u$.
Classical interlacing then gives
$(\mathscr T_n(Q/(z-\alpha_\ell)))(\beta_i)/H'(\beta_i)\ge0$.
Apply $\mathscr T_n$ to
$zQ'=rQ+\sum_\ell\alpha_\ell Q/(z-\alpha_\ell)$, using its
commutation with $zD$. This yields the model residues

$$
\frac{V(z)}{H(z)}=\sum_i\frac{w_i}{z-\beta_i},
\qquad
\frac{\beta_i}{\alpha_{\max}}\le w_i\le
\frac{\beta_i}{\alpha_{\min}},
\qquad c\le w_i\le C.
\tag{LC211}
$$

The last constants follow from the source root range and the symbol
bounds above. It does not require each cofactor to interlace strictly.

### An independent floor for the removed source factor

Fix $T\ge32$, $L=\log(T+2)$, $0<\rho\le1/8$, $\tau=T^2$ and
$R=T\rho/4$. Assume every source zero in the closed radius-$4\rho$
disc about $1/2+iT$ is on the critical line. Select them all, with
multiplicities, as $Q(z)=\prod_j(z-\gamma_j^2)$, and put $A=F/Q$.
The source count is $r\le C_0L$ and its roots lie in
$[\tau/2,2\tau]$. The pole-removal calculation (LC204) also applies
when $r=0$ or $1$; the earlier degree restriction was for the mesh model,
not for cancellation of the pole sum.
On the closed $z$ disc of radius $R$, $A$ is zero-free and the same
source estimates give

$$
|A'/A|\le B:=C L/(T\rho),\qquad
|(\log A)''|\le K:=C L/(T^2\rho^2),\qquad
|A(t)|\ge cE_Te^{-CL(1+\log(1/\rho))}(CT\rho)^{-r}
\quad(|t-\tau|\le R/2).
\tag{LC212}
$$

The last bound is independent of a source derivative at a zero.
Indeed take $h=\rho/1024$ in the already checked complete exceptional
union of (LC193)--(LC194). Its total radii are at most $h/32$,
so some point $s_a=1/2+x+iT$, $h\le x\le2h$, is outside the
entire union. Its source modulus is at least
$cE_TV_T^{-K_h}\ge cE_Te^{-CL(1+\log(1/\rho))}$.
The point $z_a=\Phi(s_a)$ lies in the radius-$R/32$ disc.
Every selected root has distance at most $CT\rho$ from $z_a$,
so division by $Q$ bounds $|A(z_a)|$ below by this floor times
$(CT\rho)^{-r}$. Integrate the already bounded $A'/A$ along the
segment from $z_a$ to $t$. Its cost is at most $CBR\le CL$.
The zero-free factor, not $F$, is used along that segment.
The same reasoning covers the empty product.

### Freeze the tangent separately at each model node

For real $t$ in $[\tau-R/2,\tau+R/2]$ put
$b(t)=A'(t)/A(t)$ and
$y(t)=t/(1+b(t)t/n)$.
Require first that $B\sigma$ and $K\sigma^2$ are sufficiently small,
$\sigma\le cR$, and $n\ge25\max(1,r)$.
These conditions imply $1+b(t)t/n$ is bounded away from zero and

$$
y'(t)=\frac{1-b'(t)t^2/n}{(1+b(t)t/n)^2}\in[1/2,2],
\qquad |y(t)-t|\le CB\sigma^2.
\tag{LC213}
$$

For every $\beta_i\in[\tau-R/4,\tau+R/4]$ there is consequently a
unique real $c_i\in[\tau-R/3,\tau+R/3]$ with $y(c_i)=\beta_i$.
Set $a_i=A(c_i)$, $b_i=b(c_i)$ and freeze
$f_i(z)=a_ie^{b_i(z-c_i)}Q(z)$.
Thus $c_i$ is exactly a node of $M_i=\mathscr T_nf_i$.
Put $U_i=\mathscr T_nf_i'$ and
$D_i=|H'(\beta_i)|=\kappa\prod_{k\ne i}|\beta_i-\beta_k|$.
For a sufficiently large absolute $C_*$ choose
$q=\min\{\delta/(C_*r),\sigma/C_*\}$ and
$I_i=[c_i-4q,c_i+4q]$.
The intervals are disjoint and contained in the working source chart,
and $q\ge c\sigma/r^{3/2}$.

The exact tilt (LC202), the root product and (LC211) give

$$
|M_i|\ge c|a_i|D_iq\quad\text{at both endpoints of }I_i,
\qquad
|M_i'|,|U_i|\ge c|a_i|D_i\quad\text{on }I_i,
\qquad M_i'U_i>0\quad\text{on }I_i.
\tag{LC214}
$$

To check the neighborhood costs, put
$y_i(t)=t/(1+b_it/n)$, whose coefficients are frozen.
On $I_i$, $|y_i(t)-\beta_i|\le8q$.
The other root factors lose at most
$(1-8q/\delta)^{r-1}$, and the off-node residue sum loses at most
$8q(r-1)\max w_i/(\delta-8q)$.
Choose $C_*$ to leave both losses below one quarter.
The $b_iH$ in $U_i$ and the $E_i'H$ in $M_i'$ cost at most
$CBq$, also small. Moreover
$E_i(t)=a_ie^{-b_ic_i}(1+b_it/n)^n$ satisfies
$c|a_i|\le|E_i(t)|\le C|a_i|$:
at $c_i$ its logarithmic attenuation is $O(B^2\sigma^2)$,
and across $I_i$ its logarithmic change is $O(Bq)$.
All differentiation of $M_i,U_i$ here keeps $a_i,b_i,c_i$ fixed.
It does not differentiate a moving choice of tangent.

### The local errors pay against the actual derivative product

Use the exact weights $\omega_0,\omega_D,\omega_G$ of (LC206).
For $u=\sqrt n|\theta|$, (LC209)--(LC210) give, uniformly for
$t\in I_i$,

$$
|Q(te^{i\theta})|
\le C\sigma D_i(\sqrt r+u)e^{Cr+C u\sqrt r}.
\tag{LC215}
$$

For clarity, each factor with $k\ne i$ is at most
$|\beta_i-\beta_k|+C\sigma(\sqrt r+u)$.
Dividing by the actual derivative product leaves
$\kappa^{-1}\prod_{k\ne i}(1+C(r+u\sqrt r)/|i-k|)$.
Its factorial denominator is $(i-1)!(r-i)!$; using
$(i-1)!(r-i)!\ge((r-1)/(2e))^{r-1}$ bounds the product by
$e^{Cr+C u\sqrt r}$. The remaining $i$ factor is at most
$C\sigma(\sqrt r+u)$.
Thus cluster spread is compared through corresponding roots, and the
factorial is retained. Replacing the derivative product by a single
worst root gap before this division would lose that comparison.

Take a fixed $\theta_0=cR/\tau\asymp\rho/T$ small enough for all
local-arc points to lie inside the source disc. The analytic logarithm
of $A$ gives
$|F(z)-f_i(z)|\le|f_i(z)|(e^{K|z-c_i|^2/2}-1)$ there.
Also $|z-c_i|\le C\sigma(1+u)$ and
$|f_i(te^{i\theta})|\le
C|a_i|e^{B t\theta^2/2}|Q(te^{i\theta})|$.
The fixed kernel supplies $|\mathcal K_n|\le C\sqrt n e^{-c_0n\theta^2}$.
For small $K\sigma^2$ and sufficiently large $n/(B\tau)$, absorb the
two quadratic factors into half this Gaussian.
The weights obey
$|\omega_D|,|\omega_G|\le C(1+u)/\sigma$.
Complete the square in
$-cu^2+Cu\sqrt r$; its remaining polynomial moments cost at most
$e^{Cr}$. Therefore the three local errors satisfy

$$
e_{0,i}^{\rm loc}\le C|a_i|D_iK\sigma^3e^{Cr},
\qquad
 e_{D,i}^{\rm loc},e_{G,i}^{\rm loc}
\le C|a_i|D_iK\sigma^2e^{Cr}.
\tag{LC216}
$$

All three integrals use the same $F-f_i$ and exact degree offsets.
No whole-circle upper bound for a derivative of $F$ is substituted.

### Pay both remote functions and exclude extra actual real nodes

On the remote arc, (LC188) bounds the original source by
$CE_T(T+2)^4e^{C(T+2)L|\theta|}$.
Its angular growth is absorbed for
$n\ge C(T+2)^2L/\rho$.
The model is bounded by
$C|a_i|(C\tau)^re^{B t\theta^2/2}$ on the entire circle, so its
quadratic growth is separately absorbed for $n\ge CB\tau$.
The remote integrals are bounded by these complete envelopes times
$C\sqrt n e^{-cn\rho^2/(T+2)^2}$; the derivative and adjacent weights
add at most $Cn/\tau$.
The independent floor (LC212),
$D_i\ge e^{-Cr}(c\sigma/\sqrt r)^{r-1}$ and
$q\ge c\sigma/r^{3/2}$ retain all normalization costs.
Together with (LC216), the actual three errors on $I_i$ consequently
have the dimensionless bound

$$
\max\left\{
\frac{\|\mathcal J_n-M_i\|_{I_i}}{|a_i|D_iq},
\frac{\|\mathcal J_n'-M_i'\|_{I_i}}{|a_i|D_i},
\frac{\|\mathcal G_n-U_i\|_{I_i}}{|a_i|D_i}
\right\}
\le CK\sigma^2e^{Cr}
+\exp\!\left[-\frac{cn\rho^2}{(T+2)^2}
+CL\{\log(n+2)+L+\log(1/\rho)\}\right]
=:\varepsilon_n.
\tag{LC217}
$$

If this is smaller than a fixed fraction of the constant in (LC214),
endpoint signs persist and the actual derivative and adjacent response
have the same fixed sign throughout $I_i$. There is exactly one actual
simple real node there and its actual product is at least
$c|a_i|^2D_i^2>0$.

This is not yet enough to identify every actual node in a central
interval. For that exclusion, at each real
$|t-\tau|\le R/16$ freeze instead the tangent at that very $t$.
Its model value is $E_tH(y(t))$, with $|E_t|\asymp|A(t)|$.
Suppose $\operatorname{dist}(y(t),\{\beta_i\})\ge q$ and choose a
nearest root $\beta_i$. Every other distance is at least
$|\beta_i-\beta_k|/2$.
Dividing the circle product by $|H(y(t))|$ now gives the same factorial
estimate as (LC215), with the remaining factor bounded by
$1+C\sigma(\sqrt r+u)/q$.
Its polynomial $r$ cost is absorbed into $e^{Cr}$.
The local relative error is thus at most $CK\sigma^2e^{Cr}$.
For the remote relative error use
$|H(y(t))|\ge\kappa q(\delta/2)^{r-1}(i-1)!(r-i)!$
and the same independent source-factor floor.
It is bounded by the remote term of (LC217).
When $\varepsilon_n<1/2$, such a point cannot be an actual node.
Every remaining actual central node has $|y(t)-\beta_i|<q$;
(LC213) places it within $2q$ of $c_i$, inside its certified $I_i$.
The associated $\beta_i$ belongs to the selected central model roots.
This covers actual real nodes, without asserting an unproved complex
root matching or zero count.

If $r=1$, use $H=z-\alpha_1$, $V=1$, $D_1=1$ and
$q=\sigma/C_*$; the same construction and exclusion have an empty
other-root product. If $r=0$, the tangent model value is the nonzero
$E_t$, and the same local and remote relative estimates exclude all
actual central nodes. These cases do not invoke a nonexistent mesh.

### A polynomial sufficient degree and an actual-node converse

There are constants $C_1,A_1>0$ for the unchanged fixed source such
that all the initial smallness conditions and the sufficient budgets
above hold for every integer

$$
n\ge C_1(T+2)^{A_1}\rho^{-A_1}
\quad\Longrightarrow\quad
\left[\ |t-T^2|\le T\rho/64,\quad
\mathcal J_n(t)=0\ \right]
\Longrightarrow\mathcal J_n'(t)\mathcal G_n(t)>0,
\tag{LC218}
$$

under the stated local all-critical-source premise.
Indeed $r\le C_0L$ makes $e^{Cr}$ at most a fixed power of $T+2$.
Choose $A_1$ greater than that power plus four and enlarge $C_1$.
This makes $K\sigma^2e^{Cr}$ small and pays $B\sigma$, the chart
clearance and both angular absorptions.
For the remote term, its exponent is decreasing once
$n\ge CL(T+2)^2/\rho^2$.
At the chosen threshold its negative term dominates
$CL\{\log(n+2)+L+\log(1/\rho)\}$ uniformly for $T\ge32$ and
$0<\rho\le1/8$. Enlarging $C_1$ pays the remaining fixed margin.
The conditions then hold for every larger $n$, not only at a
subsequence. None of these constants is numerically certified.

Taking $T=\sqrt t$, the contrapositive locates a genuine source
obstruction: if $t\ge32^2$ is an actual positive $\mathcal J_n$ node,
$\mathcal J_n'(t)\mathcal G_n(t)\le0$ and
$n\ge C_1(\sqrt t+2)^{A_1}\rho^{-A_1}$, then the closed radius-$4\rho$
disc about $1/2+i\sqrt t$ contains an actual off-line source zero.
The statement includes a zero derivative or a zero adjacent response.
It supplies neither a positive lower bound on that zero's off-line
distance nor a complex-root trajectory of the Jensen polynomial.

The winning source budget here is for centred node neighborhoods and
a central real-node exclusion; it does not establish (LC203) on its
original entire interval. Fixed $\rho$ permits a growing height
$T\lesssim n^{1/A_1}$, with an unevaluated exponent, conditional on
local source realness. It does not cover the whole unpaid interval
$t\asymp n/\log n$, certify every local premise, exclude all complex
Jensen roots or close the first-birth height/resolution obligation.
The existing fixed-band, angular-capture and defect results remain
valid independently. Full RH and strict Robin for every integer
$H>5040$ remain unresolved.


### A sharper degree payment in the actual chart resolution

The polynomial threshold in (LC218) is a sufficient coarse bound.
Keeping the same source floor, derivative product and exact angular
weights during normalization gives a smaller resolution cost.
No new general convolution, multiplier or special-function supplier
is required for this refinement. Put
$\nu=n\rho^2/T^2$, so $\sigma=T\rho/\sqrt\nu$.
All source/model definitions and the local real-source premise remain
those of (LC209)--(LC218).

The factorial in the already used derivative product gives the weaker,
but useful, uniform floor
$D_i\ge e^{-Cr}\sigma^{r-1}$.
Indeed $\delta\ge c\sigma/\sqrt r$ and
$(i-1)!(r-i)!\ge e^{-Cr}r^{r-1}$.
Thus (LC212) and $q\ge c\sigma/r^{3/2}$ give
$E_T/(|a_i|D_iq)\le e^{Cr+CL(1+\log(1/\rho))}\nu^{r/2}$,
with the polynomial $r$ factor absorbed in $e^{Cr}$.
For the derivative and adjacent errors, the corresponding normalization
is $E_T/(|a_i|D_i\sigma)$ and has the same bound.
This uses $T\rho/\sigma=\sqrt\nu$; it does not pay a separate
$r\log n$ term after that ratio has already been accounted for.

For the remote model, keep (LC215) on the entire circle instead of its
coarse maximum. Exactly,
$|\mathcal K_n|e^{b_i(t\cos\theta-c_i)}
=c_ne^{b_i(t-c_i)}e^{-(n+b_it)(1-\cos\theta)}$
with $c_n\asymp\sqrt n$.
For $u=\sqrt n\theta$, the kernel prefactor cancels with $d\theta$;
$n+b_it\ge n/2$ and the model product costs at most
$e^{Cr+C\sqrt r|u|}$ times its stated polynomial factors.
Take $\theta_0=c\rho/T$, with the same fixed small chart constant.
The model tail consequently costs $e^{Cr-c\nu}$ after completing the
square. For the actual source, the angular envelope (LC188) costs
$C\rho L|u|/\sqrt\nu$; completing its square adds only
$C\rho^2L^2/\nu$, and the Gaussian tail again costs $e^{-c\nu}$.
The original exact $\omega_D,\omega_G$ weights supply only the finite
polynomial factors $(1+|u|)/\sigma$.
Both remote functions are still included.

Together with (LC216), this sharpens (LC217) to

$$
\begin{aligned}
\max\left\{
\frac{\|\mathcal J_n-M_i\|_{I_i}}{|a_i|D_iq},
\frac{\|\mathcal J_n'-M_i'\|_{I_i}}{|a_i|D_i},
\frac{\|\mathcal G_n-U_i\|_{I_i}}{|a_i|D_i}
\right\}
\le{}&\frac{CL}{\nu}e^{Cr}\\
&+C\exp\!\left[-c\nu+
C\left\{r+L(1+\log(1/\rho))
+r\log(2+\nu)+\frac{\rho^2L^2}{\nu}\right\}\right].
\end{aligned}
\tag{LC219}
$$

For the separate pointwise-centered exclusion the nearest-root floor
is $|H(y(t))|\ge e^{-Cr}\sigma^r/r^{3/2}$ whenever its nearest distance
is at least $q$. Its extra polynomial factors are treated in precisely
the same factorial comparison, so its relative error obeys the right
side of (LC219) with a larger fixed constant.
For $r=0$ use the nonzero constant-root model and the same relative
source-floor calculation; for $r=1$ use its single-root derivative
product. Neither case requires a mesh denominator.

There is a fixed source constant $C_2$ such that the earlier central
actual-node conclusion, including $r=0,1$, holds whenever

$$
n\ge25\max(1,r),\qquad
\nu\ge C_2\left[
L e^{C_2r}+L^2+L(1+\log(1/\rho))\right].
\tag{LC220}
$$

The first term pays the local source curvature against the endpoint
and two response margins. The $L^2$ term pays $B\sigma$ and the tilt
normalization. It also pays the logarithmic root-normalization term:
for every fixed small $\eta>0$,
$r\log(2+\nu)\le\eta\nu+C_\eta r\log(2+r)$, while
$r\log(2+r)\le C(1+L^2)$ by $r\le C_0L$.
The last term pays the independent reciprocal-factor floor for
shrinking $\rho$. Increasing $C_2$ makes (LC219) smaller than every
fixed fraction used in the node and exclusion arguments, and pays
chart clearance. All inequalities remain valid for every larger
$\nu$, not only at its lower endpoint.
Unlike the coarser remote payment, completing the source's angular
square requires no separate absorption threshold (LC189).

One may replace $r$ in (LC220) by its independent count bound $C_0L$.
The resulting sufficient degree is a fixed power of height times
$\rho^{-2}$ and logarithmic resolution terms; it is more informative
than using $\rho^{-A_1}$ for all costs.
With $r$ replaced by $C_0L$ in (LC220), an actual bad node at $t=T^2$
still forces an actual
off-line source zero in the closed radius-$4\rho$ source disc by
contraposition. The sign application remains conditional on source
realness when stated forward. Neither the smaller resolution cost nor
this inverse statement gives an off-line-distance lower bound, the full
unpaid moving band, a numerical degree, RH or strict Robin for every
integer $H>5040$. The earlier thresholds remain valid independently.


## Signed finite extraction pays the growing-cluster Taylor budget

The exact tilt (LC202), root order and residues (LC209)--(LC211),
source-factor bounds (LC212), and the original circle and weights
(LC206)--(LC207) are reused. The local all-critical-source premise,
selection of every multiplicity in its closed disc, source count
$r\le C_0L$, original coefficient shift zero, and original $F$,
$\mathcal J_n$, $\mathcal G_n$ are exactly those of (LC212)--(LC220).
The arbitrary-center Poisson--Charlier supplier already cited in
[Zacharovas, Theorem 2.8](../Asymptotics/zacharovas2025depoissonization.md) supplies
the truncation-error context; its absolute coefficient remainder alone
is not a node-relative budget. Exact finite Taylor extraction here
comes from the previously established finite tilt. Only a high-order
remainder is bounded on the original circle.
The application below is repository-derived ordinary analysis; it has
no Lean, numerical-constant or originality certification. None of the
published root-order, mesh or general asymptotic results is reproved.

### The harmonic root sum sets a larger certified neighborhood

Put

$$
P=(r+1)[1+\log(r+2)]^2,\qquad
\sigma=T^2/\sqrt n,\qquad \nu=n\rho^2/T^2.
\tag{LC221}
$$

For $r\ge2$, the mesh (LC210) gives

$$
S_i:=\sum_{k\ne i}|\beta_i-\beta_k|^{-1}
\le C\sqrt P/\sigma.
\tag{LC222}
$$

Indeed sum $1/(|i-k|\delta)$, keeping its harmonic rather than
linear count. Replace the old neighborhood width only in this
application by $q=c_*\sigma/\sqrt P$, with a sufficiently small fixed
$c_*>0$, and $I_i=[c_i-4q,c_i+4q]$. The centers and frozen tangents
remain those of (LC213). Since $qS_i\le Cc_*$ and
$q\le c\delta$, the intervals remain disjoint. For
$|w-\beta_i|\le8q$, their other-root product lies between
$e^{-CqS_i}$ and $e^{CqS_i}$ times its value at $\beta_i$.
Also $\sum_{k\ne i}|w-\beta_k|^{-1}\le2S_i$.
The off-node residue sum in (LC211) and the extra $b_iH$ and
$E_i'H$ terms therefore have the same strictly smaller-than-one
relative losses as before. Thus (LC214) holds with this new $q$.
For $r=1$ take $S_1=0$, $D_1=1$ and the same formula for $q$;
its constant factor is immaterial. The empty-cluster case needs only
value exclusion. The smallness conditions imposed below pay
$B\sigma$, $K\sigma^2$ and chart clearance throughout.

### A flat analytic factor and its exact signed Taylor moments

Choose a sufficiently small fixed $a>0$ and set

$$
R_A=aT\rho/\sqrt L,\qquad
U=R_A/\sigma=a\sqrt{\nu/L},\qquad
N=\lceil D(r+1)\rceil,
\tag{LC223}
$$

where $D\ge4$ is a fixed absolute constant. Every closed
radius-$R_A$ disc around a selected $c_i$ lies inside the original
source disc. Write

$$
g_i(z)=\frac{A(z)}{a_i e^{b_i(z-c_i)}}
=1+\sum_{m\ge2}d_{m,i}(z-c_i)^m,
\qquad
P_{N,i}(z)=1+\sum_{m=2}^Nd_{m,i}(z-c_i)^m.
\tag{LC224}
$$

The source logarithm satisfies
$|\log g_i(z)|\le K|z-c_i|^2/2$ on that disc.
Since $KR_A^2\le Ca^2$, Cauchy's inequality applied to
$(g_i-1)/(z-c_i)^2$ gives

$$
|d_{m,i}|\le CKR_A^{2-m}\quad(m\ge2),\qquad
|g_i-P_{N,i}|\le CK|z-c_i|^2
\frac{(|z-c_i|/R_A)^{N-1}}{1-|z-c_i|/R_A}
\quad(|z-c_i|<R_A).
\tag{LC225}
$$

This is a factor expansion, not an expansion of $F$ about a zero
with a presumed derivative floor. Keep $a_i,b_i,c_i$ fixed and define

$$
\begin{aligned}
\mathscr M_i(s,t)
&=\mathscr T_n[e^{s(z-c_i)}f_i](t)\\
&=a_ie^{-(b_i+s)c_i}
 (1+(b_i+s)t/n)^n
 H\!\left(\frac{t}{1+(b_i+s)t/n}\right),\\
\mathscr U_i(s,t)
&=\mathscr T_n[(e^{s(z-c_i)}f_i)'](t)\\
&=a_ie^{-(b_i+s)c_i}
 (1+(b_i+s)t/n)^n
 \left[(b_i+s)H(y_s)+V(y_s)\right],
\quad y_s=\frac{t}{1+(b_i+s)t/n}.
\end{aligned}
\tag{LC226}
$$

The apparent rational expressions are polynomial identities after
cancellation, since $n\ge r$; the bounds use only discs where their
written denominator is separated from zero. Differentiating in $s$
at zero gives exactly $\mathscr T_n[(z-c_i)^mf_i]$ and
$\mathscr T_n[((z-c_i)^mf_i)']$, respectively. The latter includes
both product-rule terms. Differentiating $\mathscr M_i$ in $t$
gives the actual derivative of the extraction with all tangent
parameters still frozen. No moving tangent is differentiated.

For $2\le m\le N$, put $p_m=\sqrt m+\sqrt P$ and use the complex
$s$ circle of radius $\eta_m=m/(C\sigma p_m)$.
Assume $n\ge C N$, $B\sigma\le c$ and $U\ge C p_N$.
Then $|s|t/n\le C\sqrt{m/n}$ is small,
$|y_s-\beta_i|\le C(q+\sigma^2\eta_m)$, and

$$
\begin{aligned}
|H(w)|&\le D_i|w-\beta_i|e^{S_i|w-\beta_i|},\\
|H'(w)|&\le D_i(1+S_i|w-\beta_i|)e^{S_i|w-\beta_i|},\\
|V(w)|&\le CD_i(1+S_i|w-\beta_i|)e^{S_i|w-\beta_i|}.
\end{aligned}
\tag{LC227}
$$

The first two inequalities follow by expanding the other-root
product about $\beta_i$. For the last one expand
$V=\sum_k w_k\kappa\prod_{\ell\ne k}(w-\beta_\ell)$ and apply
(LC211); it stays valid at roots and introduces no division by a
vanishing factor. At $w=y_s$ the exponent and polynomial factors
are bounded by $e^{Cm}$, since
$S_i\sigma^2\eta_m\le Cm$.
The prefactor in (LC226), divided by $|a_i|$, is bounded by

$$
C\exp C\{\eta_m(q+B\sigma^2)+\sigma^2\eta_m^2\}
\le e^{Cm}.
$$

To see the linear term, its logarithmic $s$ derivative at zero is
$y_i(t)-c_i=O(q+B\sigma^2)$; the second derivative is
$O(\sigma^2)$ on the whole $s$ disc. Its value at zero is bounded
by the already paid $B^2\sigma^2+Bq$.
In the $t$ derivative the new factors are
$(b_i+s)/(1+(b_i+s)t/n)$ and
$(1+(b_i+s)t/n)^{-2}$; their multiplication with (LC227) adds
only $e^{Cm}$. Cauchy's inequality and $m!\le m^m$ consequently give

$$
\begin{aligned}
|\mathscr T_n[(z-c_i)^mf_i](t)|
&\le C|a_i|D_i\sigma^{m+1}(Cp_m)^{m-1},\\
|\partial_t\mathscr T_n[(z-c_i)^mf_i](t)|,
\quad |\mathscr T_n[((z-c_i)^mf_i)'](t)|
&\le C|a_i|D_i(C\sigma p_m)^m,
\qquad t\in I_i.
\end{aligned}
\tag{LC228}
$$

For the first bound, the factor
$q+\sigma^2\eta_m\le C\sigma m/p_m$ removes one power of $p_m$;
its remaining $m$ is absorbed into $C^m$. This factor matters at
endpoint normalization. Since $N\le C_D(r+1)$, $p_m\le C_D\sqrt P$.
Summing the Taylor terms with (LC225), and taking
$C_D\sigma\sqrt P/R_A<1/2$, yields

$$
\max\left\{
\frac{\|\mathscr T_n[f_i(P_{N,i}-1)]\|_{I_i}}{|a_i|D_iq},
\frac{\|\partial_t\mathscr T_n[f_i(P_{N,i}-1)]\|_{I_i}}{|a_i|D_i},
\frac{\|\mathscr T_n[(f_i(P_{N,i}-1))']\|_{I_i}}{|a_i|D_i}
\right\}
\le CK\sigma^2P.
\tag{LC229}
$$

These are signed complete-circle contributions, evaluated exactly
before bounding. No absolute contour cost $e^{Cr}$ has been paid
for the low Taylor terms.

### The high remainder and both remote functions are paid together

Choose $\theta_0=cR_A/\tau$, with $c>0$ sufficiently small.
On $|\theta|\le\theta_0$, $t\in I_i$, we have
$|te^{i\theta}-c_i|\le R_A/2$ and
$|te^{i\theta}-c_i|\le C\sigma(1+u)$, where
$u=\sqrt n|\theta|$. The former follows from $q/R_A\ll1$.
The root envelope (LC215) still holds: its proof requires only
$|t-c_i|\le C\sigma$, which the larger neighborhoods satisfy.
Apply it and the exact weights $1,\omega_D,\omega_G$ to the one
remainder $F-f_iP_{N,i}$. The local logarithmic tilt and source
curvature are absorbed into the same Gaussian as in (LC216).
Using (LC225), the three normalized local remainder errors are at most

$$
CK\sigma^2P\,
 e^{C(r+N)}
 \left[\frac{C\sqrt{r+N+1}}{U}\right]^{N-1}.
\tag{LC230}
$$

Here is the growth accounting. Before integration the value bound
contains $\sqrt P(\sqrt r+u)$ from $\sigma/q$ and (LC215),
$(1+u)^2$ from the quadratic factor, and
$[C(1+u)/U]^{N-1}$ from the Taylor remainder.
The derivative and adjacent weights add at most $C(1+u)/\sigma$.
Complete the square in $-cu^2+Cu\sqrt r$ and use its Gaussian
moment bound of degree at most $N+3$. The moment is bounded by
$e^{C(r+N)}[C\sqrt{r+N+1}]^{N-1}$ times a fixed polynomial in
$r+N+1$ and $\sqrt P$; that polynomial is absorbed into the
exponential and the displayed $P$. Thus no factorial or tail-order
cost is omitted. With $N=\lceil D(r+1)\rceil$, a sufficiently large
fixed constant in $U^2\ge CP$ makes the extra factor in (LC230)
at most one, uniformly including $r=1$.

Keep two angular cutoffs: $\theta_0=cR_A/\tau$ as above and
$\theta_R=c'R/\tau$, where $c'$ is fixed small enough for the
original source disc to contain every point with
$|\theta|\le\theta_R$, $t\in I_i$.
On $\theta_0<|\theta|\le\theta_R$ the original source satisfies
$|F(z)|\le|f_i(z)|e^{K|z-c_i|^2/2}$.
The curvature factor is absorbed into the Gaussian when
$K\sigma^2\ll1$. After (LC215) and endpoint or response normalization,
this intermediate-arc contribution is bounded by
$C\exp[-cU^2+Cr]$. Thus the independent source-factor floor need
only be paid outside the original source arc, rather than already
outside the smaller Taylor disc.

The complete model $f_iP_{N,i}$ is retained for all
$|\theta|>\theta_0$. On the entire original circle,
$|te^{i\theta}-c_i|/R_A\le C(1+u)/U$. The coefficient bound
in (LC225), without its local remainder inequality, gives

$$
|P_{N,i}(te^{i\theta})|
\le 1+CKR_A^2\sum_{m=2}^N
       (|te^{i\theta}-c_i|/R_A)^m
\le C(N+1)[1+C(1+u)/U]^N.
\tag{LC231}
$$

Use (LC215) and the full model tilt to bound this complete model.
For $u\ge cU$, the polynomial cost
$N\log[1+C(1+u)/U]$ is absorbed into a fixed fraction of $u^2$
when $U^2\ge C N$; its remaining finite constants cost $CN$.
The factors $e^{Cr+Cu\sqrt r}$ and $(1+u)$ are also absorbed,
leaving normalized model tails bounded by
$C\exp[-cU^2+C(r+N)]$ (enlarging the latter constant covers
$q^{-1}\sigma$). There is no global payment of
$(\tau/R_A)^N$: the polynomial is bounded along its Gaussian arc.

For the original source on $|\theta|>\theta_R$, use (LC188), the independent factor
floor (LC212), and the actual derivative product. The factorial in
that product gives $D_i\ge e^{-Cr}\sigma^{r-1}$, after reducing
an absolute constant. Hence
$D_iq\ge e^{-Cr}\sigma^r/\sqrt P$ up to a fixed factor.
The normalization ratio is bounded by
$\exp C\{r+L(1+\log(1/\rho))+r\log(2+\nu)\}$,
since $T\rho/\sigma=\sqrt\nu$ and $\log P\le C(r+1)$.
The source's angular term completes the Gaussian square at cost
$C(T+2)^2L^2/n\le C\rho^2L^2/\nu$.
The exact derivative weights add $(1+u)/\sigma$; their Gaussian
moments on $u\ge c\sqrt\nu$ retain $-c\nu$ after reducing $c$.
Combining (LC229)--(LC231), and $N\le C_D(r+1)$, gives

$$
\begin{aligned}
\max\left\{
\frac{\|\mathcal J_n-M_i\|_{I_i}}{|a_i|D_iq},
\frac{\|\mathcal J_n'-M_i'\|_{I_i}}{|a_i|D_i},
\frac{\|\mathcal G_n-U_i\|_{I_i}}{|a_i|D_i}
\right\}
\le{}&\frac{CLP}{\nu}\\
&+C\exp[-c\nu/L+Cr]\\
&+C\exp\!\left[-c\nu+
 C\left\{r+L(1+\log(1/\rho))+r\log(2+\nu)
       +\rho^2L^2/\nu\right\}\right].
\end{aligned}
\tag{LC232}
$$

This estimate requires $n\ge CN$, $B\sigma\le c$ and
$U^2\ge CP$; constants absorb the fixed $a,D,c_*$.
The Taylor and high-remainder terms are bounded on the same source
chart. The complete remote source and model remain in this bound.

### The query-centered exclusion still covers every central real node

At each real query $|t-\tau|\le R/16$, freeze the tangent at that
very $t$, not at a moving parameter inside a derivative.
Suppose $\operatorname{dist}(y(t),\{\beta_i\})\ge q$.
For a nearest root the other distances are at least
$|\beta_i-\beta_k|/2$, so

$$
\sum_k|y(t)-\beta_k|^{-1}\le C\sqrt P/\sigma.
\tag{LC233}
$$

With this $y=y(t)$, the polynomial product directly gives
$|H(w)/H(y)|\le\exp(C\sqrt P|w-y|/\sigma)$.
The exact generating family (LC226), now with $c=t$, therefore
bounds its signed value moments relative to $|A(t)H(y)|$ by
$[C\sigma p_m]^m$. The factor Taylor coefficients and their sum
again cost $CK\sigma^2P$.
For the high remainder a direct query-centered product estimate
is needed; the node-local envelope (LC215) is not applied outside
$I_i$. At $z=te^{i\theta}$, $u=\sqrt n|\theta|$, the paired
root displacement (LC210) gives
$|z-\alpha_k|\le|y-\beta_k|+C\sigma(\sqrt r+1+u)$,
because $|z-y|\le C\sigma(1+u)$.
Consequently, for $r\ge1$,

$$
\frac{|Q(z)|}{|H(y)|}
\le\kappa^{-1}\prod_k
 \left(1+\frac{C\sigma(\sqrt r+1+u)}{|y-\beta_k|}\right)
\le C[1+\sqrt P(\sqrt r+1+u)]e^{Cr+Cu\sqrt r}.
$$

For the nearest factor use $|y-\beta_i|\ge q$.
For $k\ne i$ use $|y-\beta_k|\ge|\beta_i-\beta_k|/2$
and the mesh, retaining $(i-1)!(r-i)!$ in the denominator.
The same factorial calculation bounds that other-root product by
$e^{Cr+Cu\sqrt r}$; $\kappa^{-1}\le e^{Cr}$ is included.
This does not require proximity of $t$ to any $c_i$.
The nearest factor's full $\sqrt r+1+u$ is retained; its fixed-degree
polynomial cost is absorbed by the $P$ and $e^{C(r+N)}$ terms in
the high-remainder calculation.
The Gaussian calculation (LC230) and the intermediate-source-arc
bound now apply to relative value error. For the complete model
tail use this same product estimate and the coefficient-based
polynomial bound (LC231) with the query's frozen center $c=t$.
Finally
$|H(y)|\ge e^{-Cr}\sigma^r/\sqrt P$ from the same nearest-root
factorial floor, so the complete remote normalization is the one
in (LC232). Its right-hand side bounds this relative error too.

Once that bound is below $1/2$, these queries cannot be actual nodes.
Every remaining actual central real node has
$|y(t)-\beta_i|<q$, so (LC213) places it within $2q$ of its
certified $c_i$. That root lies in the selected central chart.
On $I_i$, making (LC232) smaller than the fixed fractions in
(LC214) preserves both endpoint signs and both response signs.
There is exactly one actual simple real node there, and its
$\mathcal J_n'\mathcal G_n$ product is strictly positive.
For $r=1$ the same estimates use the empty other-root product.
For $r=0$, $H=1$, the query model is nonzero, its signed moments
are bounded using only the prefactor in (LC226), and the root-free
remainder and remote bounds exclude all actual central nodes.
There is no empty-mesh argument and no asserted complex-root matching.

### A polylogarithmic sufficient degree, conditional on the same source premise

A fixed source constant $C_3$ suffices for all those requirements when

$$
n\ge C_3(r+1),\qquad
\nu\ge C_3\left[ L^2[1+\log(L+2)]^2
                       +L(1+\log(1/\rho))\right].
\tag{LC234}
$$

Indeed $r\le C_0L$ gives $LP\le CL^2[1+\log(L+2)]^2$.
This pays the first term of (LC232), $U^2\ge CP$,
$B\sigma=O(L/\sqrt\nu)$, and chart clearance.
For each fixed small $\eta>0$,

$$
r\log(2+\nu)\le\eta\nu+C_\eta r\log(2+r).
$$

The second term on the right is $O(L\log(L+2))$.
The threshold pays it, $L(1+\log(1/\rho))$ and the tilt-square
cost against $\nu$ on the actual remote source arc.
Separately, its $L^2[1+\log(L+2)]^2$ term pays $Cr$ against
$\nu/L$ on the intermediate source arc and the complete model tail.
Increasing $C_3$ makes every term of the budget sufficiently small,
for every larger degree as well.
Consequently, under the explicitly unchanged premise that all source
zeros in the closed $4\rho$ disc around $1/2+iT$ are critical,

$$
\left[\ |t-T^2|\le T\rho/64,\quad\mathcal J_n(t)=0\ \right]
\quad\Longrightarrow\quad
\mathcal J_n'(t)\mathcal G_n(t)>0
\qquad\text{whenever (LC234) holds}.
\tag{LC235}
$$

With fixed $\rho$, this sufficient degree has order
$T^2\log^2T[1+\log\log T]^2$ up to unevaluated source constants,
rather than the fixed height power needed by the absolute-value
low-order envelope. The signed Taylor moments are what remove its
$e^{Cr}$ local loss; no improvement to the published mesh theorem
or root-order theorem is needed. This pays a larger conditional
height range but still falls short of the complete moving band
$t\asymp n/\log n$.

Replace $r$ in the initial degree condition by $C_0L$ before testing
an actual bad node. Then (LC234), $t=T^2$,
$\mathcal J_n(t)=0$ and $\mathcal J_n'(t)\mathcal G_n(t)\le0$
force an actual off-line source zero in that closed $4\rho$ disc
by contraposition. This is an existence conclusion, not a positive
lower bound on off-line distance or a complex-root trajectory.
The source-realness premises, all-height coverage, first-defect
closure, full RH and strict Robin for every integer $H>5040$ remain
unresolved. No unconditional height-uniform RH margin is claimed.


## Freeze at the source-circle center before transporting the actual node

The exponential-tilt identity (LC202), its signed generating-family
application (LC226)--(LC229), and the source and model bounds in
(LC209)--(LC235) are reused. The original $F$, coefficient shift zero,
$\mathscr T_n$, $\mathcal J_n$, $\mathcal G_n$ and the explicit
closed-$4\rho$-disc source-realness premise remain unchanged.
This source-specific application removes a linear-drift normalization
condition; it introduces no new generic exponential-tilt theorem.
It is ordinary analysis, with no Lean, numerical-constant or
originality certification.

The earlier tangent was fixed at its transported node $c_i$.
Instead fix it at the center of the source circle. The exponential
factor can then be removed exactly, before any endpoint, derivative
or adjacent-response estimate. Its amplitude need not be compared
with the source amplitude by a fixed constant.

### The source-to-node chart needs only $\nu$ proportional to $L$

Keep $B,K,R,\tau,\sigma,L,\nu$ from (LC212), (LC221).
For real $x$ in $[\tau-R/2,\tau+R/2]$ define

$$
b(x)=A'(x)/A(x),\qquad
h(x)=\frac{x}{1-b(x)x/n}.
\tag{LC236}
$$

For $\nu\ge C L$ with a sufficiently large fixed source constant,
$B\tau/n\le CL\rho/(T\nu)$ and $K\sigma^2\le CL/\nu$ are small.
The denominator is positive, and direct differentiation gives

$$
h'(x)=\frac{1+b'(x)x^2/n}{(1-b(x)x/n)^2}\in[1/2,2],
\qquad
|h(x)-x|\le CB\sigma^2\le CT\rho L/\nu.
\tag{LC237}
$$

Enlarge $C$ so the last displacement is at most $R/100$.
Then the chart covers all $|t-\tau|\le R/16$ and its inverse lies
in $|x-\tau|\le R/8$. These conditions do not require $B\sigma$
to be small; $B\sigma=O(L/\sqrt\nu)$ may grow.

For every selected model root $\beta_i\in[\tau-R/4,\tau+R/4]$,
put $b_i=b(\beta_i)$, $a_i=A(\beta_i)$, and

$$
g_i(z)=\frac{A(z)}{a_i e^{b_i(z-\beta_i)}},\qquad
W_i=Qg_i,\qquad
\widehat J_i=\mathscr T_n W_i,\qquad
\widehat G_i=\mathscr T_n W_i',\qquad
h_i(x)=\frac{x}{1-b_ix/n}.
\tag{LC238}
$$

The quotient $A=F/Q$ is entire after removal of the selected zeros,
so $W_i=e^{-b_i(z-\beta_i)}F/a_i$ is entire. Its definition is an
auxiliary exact factorization of the original source. Here
$g_i(\beta_i)=1$, $g_i'(\beta_i)=0$.
The node center is $t_i=h(\beta_i)=h_i(\beta_i)$.
All $a_i,b_i,\beta_i$ are frozen when the auxiliary functions are
differentiated.

### Transport all three responses before taking any absolute value

For fixed $i$, set $d_i(t)=1+b_it/n$,
$y_i(t)=t/d_i(t)$ and $E_i(t)=e^{-b_i\beta_i}d_i(t)^n$.
The exact tilt already established in (LC202), applied to $W_i$,
gives

$$
\begin{aligned}
\mathcal J_n(t)&=a_iE_i(t)\widehat J_i(y_i(t)),\\
\mathcal J_n'(t)&=a_iE_i(t)
 \left[\frac{b_i}{d_i(t)}\widehat J_i(y_i(t))
       +\frac{\widehat J_i'(y_i(t))}{d_i(t)^2}\right],\\
\mathcal G_n(t)&=a_iE_i(t)
 \left[b_i\widehat J_i(y_i(t))+\widehat G_i(y_i(t))\right].
\end{aligned}
\tag{LC239}
$$

The derivative is taken with fixed tangent parameters.
On this chart $d_i>0$ and $E_i>0$, regardless of the size of
$B\sigma$. At an actual original node the two extra multiples of
$\widehat J_i$ vanish exactly. Consequently

$$
\mathcal J_n(t)=0
\quad\Longrightarrow\quad
\mathcal J_n'(t)\mathcal G_n(t)
=\frac{a_i^2E_i(t)^2}{d_i(t)^2}
  \widehat J_i'(y_i(t))\widehat G_i(y_i(t)).
\tag{LC240}
$$

Thus the sign task and repeated-node exclusion can be paid in the
source coordinate without estimating the size of $E_i$.
No assertion that a moving choice of tangent commutes with
differentiation is used.

### Reuse the signed factor budget with zero linear drift

Take $P=(r+1)[1+\log(r+2)]^2$ and
$q=c_*\sigma/\sqrt P$, as in (LC221)--(LC222).
For $r\ge1$ put $J_i=[\beta_i-4q,\beta_i+4q]$ and
$I_i=h_i(J_i)$. The same harmonic product and bounded residues
supply

$$
|H|\ge cD_iq\ \text{at both endpoints of }J_i,\qquad
|H'|,|V|\ge cD_i,\quad H'V>0\ \text{on }J_i.
\tag{LC241}
$$

Since $t_i=h(\beta_i)$ and $h'\ge1/2$, the centers retain the
model mesh up to a fixed factor. Also $h_i'$ is bounded above
and below on its interval. Choosing $c_*$ sufficiently small makes
the $I_i$ disjoint and inside the source chart.

The expansion of $g_i$ about $\beta_i$ uses exactly (LC223)--(LC225):
$R_A=aT\rho/\sqrt L$, $U=R_A/\sigma$, $N=\lceil D(r+1)\rceil$,
$|[ (z-\beta_i)^m ]g_i|\le CKR_A^{2-m}$ for $m\ge2$.
The exact signed moments (LC228)--(LC229) now have tangent parameters
$a=1$, $b=0$, $c=\beta_i$ and query variable $x\in J_i$.
Therefore their proof requires no condition on the original $B\sigma$.
Its local contribution and the high remainder are again bounded by
$CK\sigma^2P$, once $n\ge CN$ and $U^2\ge CP$.
The intermediate source arc is bounded by
$|W_i(z)|\le|Q(z)|e^{K|z-\beta_i|^2/2}$.
The entire model Taylor-polynomial tail uses the coefficient bound
(LC231). Both tails cost $C\exp[-c\nu/L+Cr]$.
There is no linear exponential left in either auxiliary model.

On the complete remote source arc the auxiliary source instead obeys

$$
|W_i(xe^{i\theta})|
\le\frac{|F(xe^{i\theta})|}{|a_i|}
 \exp\{B|x-\beta_i|+Bx(1-\cos\theta)\}.
\tag{LC242}
$$

This retains the whole original source. The term $Bx\theta^2/2$
is absorbed into the kernel Gaussian since $B\tau/n$ is small.
The constant term on $J_i$ costs
$CBq\le CL/(\sqrt\nu\sqrt P)$; it is not discarded.
The original source's linear angular growth and the independent
factor floor are still paid as in (LC232).
The three exact weights, including the $n+1$ adjacent offset,
apply to the same auxiliary remainder $W_i-QP_{N,i}$.
Thus

$$
\begin{aligned}
\max\left\{
\frac{\|\widehat J_i-H\|_{J_i}}{D_iq},
\frac{\|\widehat J_i'-H'\|_{J_i}}{D_i},
\frac{\|\widehat G_i-V\|_{J_i}}{D_i}
\right\}
\le{}&\frac{CLP}{\nu}+Ce^{-c\nu/L+Cr}\\
&+C\exp\!\left[-c\nu+C\left\{
 r+L(1+\log(1/\rho))+r\log(2+\nu)
 +\frac{\rho^2L^2}{\nu}+\frac{L}{\sqrt\nu\sqrt P}
\right\}\right].
\end{aligned}
\tag{LC243}
$$

The assumptions here are $n\ge CN$, $\nu\ge CL$ and
$U^2\ge CP$; no $B\sigma$ smallness or source derivative floor
has been used. If the bound is a sufficiently small fixed constant,
$\widehat J_i$ has exactly one simple real node in $J_i$, and
$\widehat J_i'\widehat G_i>0$ there by (LC241).
Equation (LC240) transports the same conclusion to $I_i$.

### Query-centered exclusion retains every actual central real node

For a central original query $t$, let $x=h^{-1}(t)$, freeze
$b=b(x)$, $a=A(x)$ at this physical source coordinate, and set
$g_x(z)=A(z)/(a e^{b(z-x)})$.
The value identity (LC239) uses $y(t)=x$ and
$\widehat J_x=\mathscr T_n(Qg_x)$.
This is only a pointwise value comparison; no moving tangent is
differentiated.
If $\operatorname{dist}(x,\{\beta_i\})\ge q$, the reciprocal-root
sum and the direct full-circle $Q/H(x)$ product comparison proved
following (LC233) apply at this $x$. The signed factor sum, high
remainder, intermediate arc and entire polynomial-model tail have
the same relative value bounds as (LC243).
For the remote source (LC242) its constant term is now zero because
the circle center and tangent center are both $x$.
The factorial floor for $|H(x)|$ is unchanged. Hence such a query
cannot be an original node when (LC243) is below $1/2$.

Every remaining actual central node has $|x-\beta_i|<q$ for a
selected central root. Its center is $t_i=h(\beta_i)$, so
$|t-t_i|\le2q$ by (LC237). More explicitly

$$
|h(x)-h_i(x)|\le C\sigma^2K|x-\beta_i|,
\tag{LC244}
$$

using $|b(x)-b_i|\le K|x-\beta_i|$ and the two bounded
denominators. Thus $t=h(x)$ lies inside the image $I_i=h_i(J_i)$
when $K\sigma^2$ is small: the inverse $y_i$ has bounded derivative,
so $|y_i(t)-\beta_i|<4q$.
This places every actual central node in its certified interval.
For $r=1$, the same statements use the empty other-root product.
For $r=0$ use $H=Q=1$ and the nonzero query model; the relative
value bound excludes all central actual nodes without a mesh or $D_i$.

### A source-count-adaptive sufficient degree

A sufficiently large fixed source constant $C_4$ pays every initial
condition and every term of (LC243) when

$$
n\ge C_4(r+1),\qquad
\nu\ge C_4\left[
 L(r+1)[1+\log(r+2)]^2+L(1+\log(1/\rho))\right].
\tag{LC245}
$$

The first term pays the signed local error, $U^2\ge CP$, the
intermediate exponent and all finite Taylor-order conditions.
It implies $\nu\ge CL$, so it pays chart clearance and
$K\sigma^2$, $B\tau/n$ smallness.
For the remote exponent use
$r\log(2+\nu)\le\eta\nu+C_\eta r\log(2+r)$.
Its last term is dominated by $LP$; the independent factor floor
is paid by the second term of (LC245).
Also $\rho^2L^2/\nu\le CL/P$ and
$L/(\sqrt\nu\sqrt P)\le C\sqrt L/P$; both are absorbed by
$-c\nu$ after enlarging $C_4$.
All bounds remain controlled for every larger degree, rather than
only at the threshold. Under the explicitly unchanged local
all-critical-source premise, they therefore give

$$
\left[\ |t-T^2|\le T\rho/64,\quad\mathcal J_n(t)=0\ \right]
\quad\Longrightarrow\quad
\mathcal J_n'(t)\mathcal G_n(t)>0
\qquad\text{whenever (LC245) holds}.
\tag{LC246}
$$

For independently bounded $r\le\bar r$, this sufficient degree,
with fixed $\rho$, has order $T^2\log T$, with constants depending
on $\bar r$ and $\rho$. More generally (LC245) keeps the actual
source count in the budget. No uniform bounded source count is
asserted at all heights or supplied by the local realness premise.
An independently certified upper bound for all source multiplicities
in the disc may replace $r$ before a bad-node inverse test.
The universal count $r\le C_0L$ recovers the earlier worst-case
$T^2\log^2T[1+\log\log T]^2$ sufficient order.

The linear-drift cost is therefore removable by exact source-centered
transport. The growing-cluster curvature cost $K\sigma^2P$ remains;
it has not been removed by renaming the auxiliary source or by
bounding $E_i$. A quadratic or more accurate local model would still
need its own actual-node margins, all-response finite extraction
comparison, complete tails and query exclusion.
The whole unpaid moving band, source-realness certification,
first-defect closure, RH and strict Robin for every integer $H>5040$
remain unresolved. This application asserts no global Jensen-root
matching or numerical degree.


## A quadratic tangent leaves a distinct same-source high-order obligation

The source-centered budget (LC245) removes the unnecessary linear-drift
normalization condition. For growing clusters, its remaining curvature
cost suggests incorporating a quadratic source factor into the local
model. The exact Gaussian identity needed for that model already exists;
it does not control the actual source's higher-order factor.
The following application and countermodel distinguish those obligations.
They are ordinary analysis without Lean, numerical-constant or originality
certification, and do not assert a counterexample to RH or to actual-node
positivity of the original $\Xi$ source.

### Reuse the published quadratic identity with its actual coordinates

Hall--Ho--Jalowy--Kabluchko,
[*The heat flow, GAF, and $SL(2,\mathbb R)$*, arXiv:2304.06665v2](https://arxiv.org/html/2304.06665v2),
Proposition 2.8, equation (2.13), gives the exponential-quadratic
conjugacy for the heat operator. Its hypothesis is a finite order-two
type bound (2.2), with heat time less than
$1/(2\sigma_0+|a|)$. A polynomial has type $\sigma_0=0$, so for
real $a,b$, $h>0$, $|a|h<1$, the cited theorem applies directly.
With $x=t-c$, $\widetilde Q(x)=Q(c+x)$, put

$$
\begin{aligned}
\mathcal H_h&=e^{-hD^2/2},\qquad d=1+ah>0,\qquad v=h/d,\qquad
 y=(x-bh)/d,\\
P(y)&=\mathcal H_v\widetilde Q(y),\\
E(x)&=\frac{A(c)}{\sqrt d}
 \exp\!\left(\frac{ax^2+2bx-hb^2}{2d}\right).
\end{aligned}
\tag{LC247}
$$

For the frozen model
$f(c+x)=A(c)e^{bx+ax^2/2}\widetilde Q(x)$, that published identity
states $\mathcal H_hf(c+x)=E(x)P(y)$.
Its amplitude, effective heat time and physical coordinates must all
be transported. In particular $E(0)/A(c)=d^{-1/2}e^{-hb^2/(2d)}$.
If the polynomial $P$ has a simple root $\beta_i$, the corresponding
physical model node and its derivative are

$$
t_i=c+bh+d\beta_i,\qquad
(\mathcal H_hf)'(t_i)=E(t_i-c)P'(\beta_i)/d.
\tag{LC248}
$$

The heat operator commutes with differentiation, so its adjacent
response equals this same derivative. The physical separation is
$d|\beta_i-\beta_j|$, not just the separation in the $y$ coordinate.
These are direct parameter applications of the cited formula;
no generic heat-flow theorem is reproved or presented as new.
They do not imply global hyperbolicity of the finite Jensen extraction:
for instance $\mathscr T_2(e^{az^2/2})=1+az^2/4$ has nonreal roots
when $a>0$.

For the actual $F$, a comparison with this Gaussian model splits into

$$
\begin{aligned}
\mathcal R_nF-\mathcal R_{\rm G}f
&=\mathcal R_n(F-f)+(\mathcal R_nf-\mathcal R_{\rm G}f),\\
\mathcal R_nu&=(\mathscr T_nu,D\mathscr T_nu,\mathscr T_nDu),\qquad
\mathcal R_{\rm G}f=(\mathcal H_hf,D\mathcal H_hf,D\mathcal H_hf).
\end{aligned}
\tag{LC249}
$$

The second term is a finite-operator/Gaussian comparison.
The first is the original source's tangent remainder, with its own
signed low terms and complete tails. Paying the second term cannot
remove the first. The countermodel below makes the first term large
in the proposed derivative-product units, even with no linear or
quadratic source drift.

### A locally real cluster with zero quadratic jet

Fix $\rho=1/64$ and $C_*>0$. Let $T\to\infty$,
$L=\log(T+2)$, and let $r$ be odd with $r/L\to\epsilon>0$,
where $\epsilon$ is small enough for $r\le C_0L$.
Put $c=T^2$, $R=T\rho/4$,
$n=\lceil C_*T^2L/\rho^2\rceil$,
$\sigma=c/\sqrt n$, $\nu=n\rho^2/T^2$, and

$$
D_0=16T\rho=64R,\qquad
Q_*(z)=(z-c)^r,\qquad
A_*(z)=\left[1+\frac{(z-c)^4}{D_0^4}\right]^r,
\qquad F_*=A_*Q_*.
\tag{LC250}
$$

On $|z-c|\le R$, with $w=z-c$, the factor is zero-free and

$$
\begin{aligned}
|A_*(z)|&\ge(1-64^{-4})^r,\\
A_*'/A_*&=\frac{4rw^3}{D_0^4+w^4},\\
(\log A_*)''&=\frac{12rw^2}{D_0^4+w^4}
             -\frac{16rw^6}{(D_0^4+w^4)^2}.
\end{aligned}
\tag{LC251}
$$

The two derivatives have the same upper orders
$CL/(T\rho)$ and $CL/(T^2\rho^2)$ as (LC212), and the first
line is an independent nonvanishing floor. At the center,
$A_*(c)=1$ and $(\log A_*)'(c)=(\log A_*)''(c)=0$.
Thus its quadratic tangent is exactly $Q_*$.
All zeros of $A_*$ lie at distance $D_0$ from $c$.
Under the original map $z=-(s-1/2)^2$, points
$s=1/2+iT+u$, $|u|\le4\rho$, satisfy
$|z-c|\le8T\rho+16\rho^2<D_0$ for large $T$.
The closed source disc therefore contains only the central critical-line
zero, with multiplicity $r$; the extra nonreal zeros are outside it.
This verifies the actual local zero geometry instead of stipulating
it for an unrelated formal factor.

This family is a countermodel to an inference from just the displayed
local factor data. It is not the original $\Xi$, its theta kernel,
or a certificate of the original complete remote-source envelope.
Multiplying both $F_*$ and its model by a nonzero real scalar leaves
all relative derivative comparisons below unchanged. A scalar amplitude
floor alone therefore cannot remedy this local obstruction.

### The signed Gaussian derivative already has exponential amplification

Set $M=\mathcal H_{\sigma^2}Q_*$.
The classical probabilists' Hermite polynomial normalization used in
(LC24)--(LC26) gives
$\mathcal H_{\sigma^2}(z-c)^m
=\sigma^m\operatorname{He}_m((z-c)/\sigma)$.
Since $r$ is odd, $c$ is a simple model root and
$M'(c)=\sigma^{r-1}\operatorname{He}_r'(0)\ne0$.
Expand the finite polynomial $F_*$ from (LC250).
The exact Hermite coefficients at zero give

$$
\begin{aligned}
\frac{\operatorname{He}_{r+4j}'(0)}{\operatorname{He}_r'(0)}
 &=\prod_{k=1}^{2j}(r+2k)>0,\\
\frac{(\mathcal H_{\sigma^2}F_*)'(c)}{M'(c)}
 &=\sum_{j=0}^r\binom rj
   \left(\frac\sigma{D_0}\right)^{4j}
   \prod_{k=1}^{2j}(r+2k)
 \ge\left(1+\frac{\sigma^4r^2}{D_0^4}\right)^r.
\end{aligned}
\tag{LC252}
$$

All summands have the same sign; this is an actual signed response,
not an absolute-contour upper bound. Now
$\sigma^4r^2/D_0^4=r^2/(16^4\nu^2)
\to\epsilon^2/(16^4C_*^2)>0$.
The ratio in (LC252) grows at least exponentially in $r$.
The Gaussian model derivative floor $|M'(c)|$ thus fails to normalize
the original-source derivative remainder to a small quantity at
$\nu\asymp C_*L$, even though the quadratic jet is zero.
The fourth-order logarithmic coefficient is $r/D_0^4$;
on the cluster scale $\sigma\sqrt r$ its magnitude is
$\sigma^4r^3/D_0^4\asymp L$, not a vanishing quantity.

### The same obstruction survives the complete finite extraction

Write $p_m(z)=(z-c)^m$. The already established exact exponential
extraction gives
$\sum_m\mathscr T_np_m(t)u^m/m!=e^{-cu}(1+tu/n)^n$.
Set $w=\sigma u$ and differentiate with all parameters fixed.
The two complete finite response generators at $t=c$ are

$$
\begin{aligned}
\sum_{m\ge0}\frac{(\mathscr T_np_m)'(c)}{\sigma^{m-1}}
 \frac{w^m}{m!}
 &=w e^{-\sqrt n w}(1+w/\sqrt n)^{n-1},\\
\sum_{m\ge0}\frac{\mathscr T_n(p_m')(c)}{\sigma^{m-1}}
 \frac{w^m}{m!}
 &=w e^{-\sqrt n w}(1+w/\sqrt n)^n.
\end{aligned}
\tag{LC253}
$$

Uniformly over the odd $1\le m\le5r$, these imply

$$
(\mathscr T_np_m)'(c),\quad \mathscr T_n(p_m')(c)
=\sigma^{m-1}\operatorname{He}_m'(0)
       [1+O(r^2/\sqrt n)].
\tag{LC254}
$$

For completeness this is a coefficient estimate at a fixed center,
not a general growing-degree Charlier theorem. For $m>1$ let
$k=m-1$, which is even, and use the Cauchy circle $|w|=\sqrt k$.
For $\ell=0,1$,
$-\sqrt n w+(n-\ell)\log(1+w/\sqrt n)
=-w^2/2+O(k^{3/2}/\sqrt n)$ uniformly on that circle.
The error is small because $r^3/n\to0$.
The exact comparison coefficient is
$[w^k]e^{-w^2/2}=(-1)^{k/2}/(2^{k/2}(k/2)!)$.
Cauchy's bound on the difference is
$k^{-k/2}e^{k/2}O(k^{3/2}/\sqrt n)$.
Dividing by the exact coefficient and applying Stirling increases
this by only $O(\sqrt k)$, proving $O(k^2/\sqrt n)$.
The case $m=1$ is exact. These bounds are uniform across all
$r+4j$, $0\le j\le r$, and keep their signed Hermite coefficients.

For $J_* =\mathscr T_nF_*$, $G_* =\mathscr T_nF_*'$,
linearity and the same-sign expansion (LC252) consequently give

$$
\frac{J_*'(c)}{M'(c)},\qquad\frac{G_*(c)}{M'(c)}
\ge [1-O(r^2/\sqrt n)]
 \left(1+\frac{\sigma^4r^2}{D_0^4}\right)^r
\longrightarrow+\infty.
\tag{LC255}
$$

The same conclusion holds if the denominator is replaced by the
finite-model response $(\mathscr T_nQ_*)'(c)$ or
$\mathscr T_nQ_*'(c)$, respectively, since (LC254) compares those
with $M'(c)$ by a factor tending to one.
No circle arc or source/model tail is omitted: (LC253) is an exact
finite coefficient identity. The physical center $c$ need not be a
zero of $J_*$, and its two derivative responses amplify with the same
sign. Thus (LC255) refutes only the proposed relative derivative
smallness from the listed local data, not actual-node positivity,
original-source RH, or the finite source-centered budget (LC245).

The remaining route must use additional structure of the same original
$\Xi$ factor, or absorb its signed high-order contributions into a
common nonvanishing response amplitude with controlled variation.
A standalone finite/Gaussian comparison for the quadratic tangent
would leave the first term of (LC249) unpaid.
That same-source amplitude construction, growing-cluster actual-node
margins and query exclusion at the complete moving scale remain open.
RH and strict Robin for every integer $H>5040$ remain unresolved.


## Same-source amplitude gives an actual node in the quartic obstruction

The obstruction (LC250)--(LC255) concerns small error measured against a
quadratic tangent. It leaves the actual-node sign unanswered.
For that same finite source, the signed contributions can instead be
kept in one common derivative amplitude. This application reuses the
complete finite generators (LC253) and the classical Hermite coefficients
already used in (LC252)--(LC254). The additional estimate is uniform on
a neighborhood and produces an actual finite node; it is not another
generic heat identity or a claim of a new published theorem.
The argument is ordinary analysis without Lean, numerical-constant or
originality certification.

### Keep all contributions of one odd congruence class

Let $r\ge1$ be odd, $c>0$, let $n$ be a positive integer with
$n\ge M=r+4J$, and take a finite source

$$
\begin{aligned}
P(z)&=\sum_{j=0}^J a_j(z-c)^{m_j},\qquad m_j=r+4j,\\
a_j&\ge0,\qquad \sum_j a_j>0,\qquad \sigma=c/\sqrt n,\\
J_P&=\mathscr T_nP,\qquad G_P=\mathscr T_nP',\\
\mathcal D_P&=\sum_j a_j\sigma^{m_j-1}\operatorname{He}_{m_j}'(0).
\end{aligned}
\tag{LC256}
$$

All $\operatorname{He}_{m_j}'(0)$ have sign $(-1)^{(r-1)/2}$.
Consequently $|\mathcal D_P|$ equals the sum of the moduli of its
summands and is strictly positive. The coefficients may depend on
$c,n,M$; none of the following constants depends on them.
This amplitude uses the entire finite source, not its quadratic jet.

Fix $\eta=1/4$ and write $t=c+\sigma v$ with
$|v|\le\eta/\sqrt M$. The interval is positive.
For odd $m=2k+1$ put $Z_m(v)=\operatorname{He}_m(v)/
\operatorname{He}_m'(0)$. The already used Hermite coefficient formula
and its derivative give

$$
\begin{aligned}
Z_m'(v)&=\sum_{\ell=0}^k
 \frac{(-1)^\ell2^\ell(k)_{\underline\ell}v^{2\ell}}{(2\ell)!},\\
|Z_m'(v)-1|&\le\cosh(\sqrt{m-1}|v|)-1
 \le\cosh\eta-1<1/8,\qquad Z_m(0)=0.
\end{aligned}
\tag{LC257}
$$

Thus $\mathcal H_{\sigma^2}P$ has derivative with
$\mathcal D_P$'s sign and modulus at least $7|\mathcal D_P|/8$
on this whole interval. Its endpoint values have the respective signs
of $\pm\mathcal D_P$, with modulus at least
$7\sigma|\mathcal D_P|\eta/(8\sqrt M)$.
These margins sum same-sign source responses; they do not compare
against the unamplified tangent derivative.

### Extend the complete finite coefficient estimate to that interval

For $p_m(z)=(z-c)^m$ put
$E_{n,v}(w)=e^{-\sqrt n w}(1+w/\sqrt n+vw/n)^n$.
The exact generating identity behind (LC253), now evaluated at $t$, is

$$
\begin{aligned}
\sum_m\frac{\mathscr T_np_m(t)}{\sigma^m}\frac{w^m}{m!}
 &=E_{n,v}(w),\\
\sum_m\frac{(\mathscr T_np_m)'(t)}{\sigma^{m-1}}\frac{w^m}{m!}
 &=w e^{-\sqrt n w}(1+w/\sqrt n+vw/n)^{n-1},\\
\sum_m\frac{\mathscr T_np_m'(t)}{\sigma^{m-1}}\frac{w^m}{m!}
 &=w E_{n,v}(w).
\end{aligned}
\tag{LC258}
$$

For every odd $3\le m\le M$, use the Cauchy circle
$|w|=\sqrt k$, $k=m-1$. Uniformly in this $v$ interval and
$\ell=0,1$,
$-\sqrt n w+(n-\ell)\log(1+w/\sqrt n+vw/n)
=vw-w^2/2+O(m^{3/2}/\sqrt n)$.
Under $M^2/\sqrt n$ sufficiently small, the logarithm has its analytic
branch on the disc and the error tends uniformly to zero.
The Gaussian modulus on the circle is at most $e^{k/2+\eta}$.
Cauchy's coefficient bound, divided by the exact normalization
$|\operatorname{He}_m'(0)|=m!/[2^{k/2}(k/2)!]$, gives

$$
\begin{aligned}
\frac{|\mathscr T_np_m(t)/\sigma^m-\operatorname{He}_m(v)|}
 {|\operatorname{He}_m'(0)|}
 &\le C m^{3/2}/\sqrt n,\\
\frac{|(\mathscr T_np_m)'(t)/\sigma^{m-1}-\operatorname{He}_m'(v)|}
 {|\operatorname{He}_m'(0)|}
 &\le C m^2/\sqrt n,\\
\frac{|\mathscr T_np_m'(t)/\sigma^{m-1}-\operatorname{He}_m'(v)|}
 {|\operatorname{He}_m'(0)|}
 &\le C m^2/\sqrt n.
\end{aligned}
\tag{LC259}
$$

For the value, the coefficient normalization costs only
$2^{k/2}(k/2)!k^{-(k+1)/2}e^{k/2}=O(1)$.
For either derivative the extra $w$ raises that cost to $O(\sqrt k)$,
as in (LC254). There is no exponential comparison loss.
All three formulas are exact at $m=1$.
No source or model arc is removed; these are complete polynomial
coefficients, including the original derivative and adjacent response.

### The normalization now pays endpoint and actual-node margins

Sum (LC259) with the coefficients in (LC256). Sign coherence gives

$$
\begin{aligned}
|J_P-\mathcal H_{\sigma^2}P|
 &\le C\sigma|\mathcal D_P|M^{3/2}/\sqrt n,\\
|J_P'-(\mathcal H_{\sigma^2}P)'|
 +|G_P-(\mathcal H_{\sigma^2}P)'|
 &\le C|\mathcal D_P|M^2/\sqrt n.
\end{aligned}
\tag{LC260}
$$

There is a sufficiently small absolute $c_\eta>0$ such that
$M^2/\sqrt n\le c_\eta$ makes the value error smaller than both
endpoint margins and makes each response error at most
$|\mathcal D_P|/8$. The derivative and adjacent response then have
$\mathcal D_P$'s sign and modulus at least $3|\mathcal D_P|/4$
on the entire interval. The endpoint signs and strict monotonicity
therefore supply exactly one actual real simple $J_P$ node $t_*$ there,
with

$$
\begin{aligned}
J_P'(t_*)G_P(t_*)&\ge9|\mathcal D_P|^2/16>0,\\
|t_*-c|&\le C\sigma M^{3/2}/\sqrt n.
\end{aligned}
\tag{LC261}
$$

The displacement follows from the value error at $c$ and the same
nonzero derivative bound. The assertion is about this central interval;
it makes no claim about the remaining roots or all degrees.

For the actual quartic family (LC250), take
$a_j=\binom rjD_0^{-4j}$ and $M=5r$. At fixed $\rho$, with
$r\sim\epsilon\log T$ and $n\sim C_*T^2\log T/\rho^2$,
$M^2/\sqrt n=O(\log^{3/2}T/T)\to0$.
Thus (LC261) applies for all sufficiently large $T$.
The interval lies inside $|t-c|\le T\rho/64$ eventually, since
$\sigma\eta/(\sqrt M T\rho)=\eta/\sqrt{\nu M}\to0$.
Meanwhile (LC252) gives
$|\mathcal D_P|/|\sigma^{r-1}\operatorname{He}_r'(0)|\to\infty$
at least exponentially in $r$.
The same source therefore has a strict actual-node positive margin
even while its tangent-normalized derivative error grows exponentially.
This does not weaken the earlier obstruction: it answers a different,
stronger node question with a different independently nonzero amplitude.

The restricted nonnegative coefficients in one odd congruence class
are the load-bearing source structure. They have not been established
for the original $\Xi$ factor. Its mixed parity and opposite-congruence
contributions, infinite remainder and complete source tails still need
joint signed control, with a nonzero shared response amplitude and
coverage of every actual node in the full moving band.
Local $B,K$ bounds alone do not supply those properties.
This finite-model application certifies neither original-source local
realness at every height, global Jensen hyperbolicity, RH nor strict
Robin for every integer $H>5040$.


## Retain absolute exterior-zero mass from the original source count

The local logarithmic curvature in (LC204)--(LC205) is a signed
complex sum. It need not measure the exterior zeros' total influence.
The complete fixed-source count in (LC180) supplies an additional
initial estimate without assuming that the exterior zeros are real.
This is a source-specific application of the existing count and
canonical-product suppliers, not a new zero-count theorem. The
estimates below are ordinary analysis without Lean or originality
certification; their propagation to actual finite nodes remains open.

Retain $T\ge32$, $L=\log(T+2)$, $0<\rho\le1/8$, $c=T^2$,
$R=T\rho/4$, a positive integer $n$, $\sigma=c/\sqrt n$ and
$\nu=n\rho^2/T^2$. Use the same conditional local premise as (LC204): every source zero
in the closed radius-$4\rho$ disc about $1/2+iT$ is critical, and
$Q$ removes all of them with their full multiplicities. Set $A=F/Q$.
Every sum below counts multiplicities and includes every exterior
zero of the unchanged entire source $F$.

### Use the full count before taking an absolute value

Represent a zero $\zeta$ of $F$ by $\zeta=t_\zeta^2$, where
$t_\zeta=\gamma+i\eta$, $\gamma>0$ and $|\eta|<1/2$.
This selects the positive-ordinate source zero once, rather than
counting both square-root signs. On $|z-c|\le R$ take the local
square root $t_z$ with positive real part. Then

$$
|t_z-T|\le\rho/4,\qquad
|z-\zeta|=|t_z-t_\zeta|\,|t_z+t_\zeta|,
\qquad |t_z+t_\zeta|\ge T-\rho/4+\gamma.
\tag{LC262}
$$

Every unremoved source zero has $|t_\zeta-T|>4\rho$, hence its
distance from this working $z$ disc is at least $3T\rho$.
The upper-count argument of (LC180) applies at every height
$u\ge32$: it uses the Euler-anchored normalization at $2+iu$,
not the conditional existence of an off-line zero. It gives
$O(\log(u+2))$ zeros in each fixed unit-height window. Fixed low
heights contribute a finite constant. Summing those same window
counts also gives $N(U)=O(U\log(U+2))$.

For $|\gamma-T|\le2$, the complete count is $O(L)$ and the
clearance just obtained gives $CL/(T^2\rho^2)$. For comparable
heights $T/2\le\gamma\le2T$ outside that near window, (LC262)
gives $|z-\zeta|\ge c_1T|\gamma-T|$; the unit windows sum to
$CLT^{-2}\sum_{k\ge1}k^{-2}$. Zeros below $T/2$ cost
$O(L/T^3)$, using $N(T/2)=O(TL)$ and distance $\gg T^2$.
Those above $2T$ cost the same order by summing
$O(\log(k+2))k^{-4}$ over $k\ge2T$. Consequently

$$
\mathcal K_{\rm abs}:=
\sup_{|z-c|\le R}
\sum_{\zeta\in Z(F)\setminus Z(Q)}\frac1{|z-\zeta|^2}
\le \frac{C_{\rm abs}L}{T^2\rho^2},\qquad
\sigma^2\mathcal K_{\rm abs}\le C_{\rm abs}\frac L\nu.
\tag{LC263}
$$

The constants depend on the fixed original source and windows,
not on $n$, $\rho$, the selected multiplicities or their spacings.
All exterior-zero sums are absolute. In particular, at
$\nu\sim C_*L$, their scaled mass has limsup at most
$C_{\rm abs}/C_*$; it can be made small by choosing a sufficiently
large fixed degree constant. This is an initial-source estimate, not an evolving-zero
or extracted-response estimate.

### What this mass supplies to every higher logarithmic jet

The source's order-$1/2$ square shadow is already recorded in
[the Jensen supplier](../Zeros/osullivan2021modifiedjensen.md).
Reuse the classical genus-zero canonical product; no new
factorization theorem is asserted. Removing the finite factor $Q$
leaves the exterior-zero product. The finite partial-fraction and
central-moment identities are already present in
`D5/S3/Analytic/FiniteGenusZeroMomentExpansion`; they are not new
formalization targets. The infinite convergence and source estimate
here are ordinary analytical obligations. With $D=3T\rho$,
$b=A'(c)/A(c)$ and $\kappa_c=\sum_{\rm ext}|c-\zeta|^{-2}$,
termwise logarithmic differentiation gives

$$
\left|(\log A)^{(k)}(c)\right|
\le (k-1)!\frac{\kappa_c}{D^{k-2}}
\quad(k\ge2),\qquad \kappa_c\le\mathcal K_{\rm abs}.
\tag{LC264}
$$

Indeed the exact derivative is
$(-1)^{k-1}(k-1)!\sum_{\rm ext}(c-\zeta)^{-k}$.
The canonical product converges locally, and these differentiated
sums converge absolutely. In the disc $|w|<D$, use the analytic
logarithm equal to zero at $w=0$. The same exterior factors yield

$$
\begin{aligned}
\log\frac{A(c+w)}{A(c)}-bw
 &=\sum_{\rm ext}\left[
 \log\left(1+\frac{w}{c-\zeta}\right)
                   -\frac{w}{c-\zeta}\right],\\
\left|\log\frac{A(c+w)}{A(c)}-bw\right|
 &\le \frac{\kappa_c|w|^2}{2(1-|w|/D)}.
\end{aligned}
\tag{LC265}
$$

This retains absolute zero mass as well as signed jets. It does
not make the logarithmic remainder uniformly small on the cluster
scale $|w|\asymp\sigma\sqrt r$. When $|w|/D\le q<1$ with fixed
$q$, its upper order there is $r\sigma^2\mathcal K_{\rm abs}$,
which can grow with $r$; without that restriction retain the full
denominator in (LC265).

### Small absolute mass still does not repair tangent normalization

The already analysed quartic family (LC250) makes this distinction
explicit without constructing another model. Its $4r$ exterior
zeros all have distance $D_0=16T\rho$ from $c$. Thus

$$
\sigma^2\kappa_{*,c}=\frac r{64\nu},\qquad
\sigma^2\mathcal K_{*,\rm abs}
\le\frac r{64\nu}\left(\frac{64}{63}\right)^2.
\tag{LC266}
$$

Here the supremum uses the same radius $R=D_0/64$.
For $r/L\to\epsilon>0$ and $\nu\sim C_*L$, this mass can be
made smaller than any prescribed positive constant by a large
fixed $C_*$. Nevertheless, for each such fixed $C_*$ the signed
derivative ratio in (LC252) still diverges, since its lower bound is
$[1+r^2/(16^4\nu^2)]^r$. The complete finite responses and the
actual central-node conclusion keep the distinct scopes established
in (LC255)--(LC261). This observation excludes an inference from
small absolute mass to small tangent-relative derivative error;
it does not refute actual-node positivity or identify this model
with the original $\Xi$.

### Published local dynamics leave a propagation obligation

Polymath, [arXiv:1904.12438v2](https://arxiv.org/html/1904.12438v2),
Proposition 3.1 supplies the instantaneous simple-zero velocity
and Hermite splitting of a repeated zero for its original-variable
heat flow. Its repeated-zero error may depend on the multiplicity;
Proposition 3.3 additionally requires initial, terminal and whole-time
zero-free barriers. These are published suppliers, not a uniform
continuation theorem under just (LC263). Squaring the original
variable also changes the heat generator.

Höfert--Jalowy--Kabluchko,
[arXiv:2512.17808v2](https://arxiv.org/html/2512.17808v2),
Lemma 3.12 and Remark 3.13 allow complex initial roots, but their
finite heat localization radius depends on the entire polynomial
degree. It cannot be replaced by the selected local count $r$ or
applied to an infinite source by discarding its distant zeros.
Hall--Ho--Jalowy--Kabluchko's order-less-than-one instantaneous
root-velocity supplier likewise does not identify the heat operation
with $\mathscr T_n$.

The remaining task is to propagate the same original source's
absolute exterior mass and complete tails to a nonvanishing response
amplitude or direct actual-node estimate, uniformly for growing
selected multiplicity. A heat route must also pay the evolving
barriers and the finite-extraction comparison. Equations (LC263)--
(LC265) provide initial data for that task, not its solution.
RH and strict Robin for every integer $H>5040$ remain unresolved.


## Conditional exterior nonvanishing at sufficiently large finite degree

Under the local critical-zero and complete-removal premises in (LC263),
its original-source mass bound and the drift bound in (LC205) supply a
zero-free certificate for the finite extraction of the complete exterior
factor at the sufficiently large degree specified in (LC270). This is a repo-derived
analytical application of the existing genus-zero product, coefficient
circle (LC176) and exponential tilt (LC202). These suppliers are reused,
not new factorization or depoissonization theorems. The certificate is
for $\mathscr T_nA$, not $\mathscr T_n(AQ)$; it carries neither Lean
certification nor an originality claim.

The real transport chart and empty-selection real-node exclusion were
already documented in (LC236)--(LC246). The additional application here
is the complete exterior-product estimate on the full coefficient circle
and nonvanishing throughout the actual complex target disc.

Retain every hypothesis and parameter of (LC263), in particular the
conditional critical-line premise for every zero in the closed selected
source disc and its complete removal in $Q$. Put $D=T\rho$, so the
working disc in (LC263) has radius $D/4$. The $D$ here is not the
clearance $3T\rho$ used in (LC264). All exterior zeros and their
multiplicities remain in $A=F/Q$.
For an entire function $H(z)=\sum_{k\ge0}h_kz^k$, the same finite
extraction is $\mathscr T_nH(z)=\sum_{k=0}^n(n)_{\underline k}n^{-k}h_kz^k$.
This extends the existing coefficient definition, without changing the
operator or introducing a coefficient shift.

### A global remainder pays the full coefficient circle

For $A(a)\ne0$ write
$b_a=A'(a)/A(a)$, $K_a=\sum_{\zeta\in Z(A)}|a-\zeta|^{-2}$ and
$g_a(z)=A(z)/(A(a)e^{b_a(z-a)})$.
The order-less-than-one canonical product used in (LC264) gives
$g_a(a+w)=\prod_{\zeta\in Z(A)}E(w/(a-\zeta))$, where
$E(u)=(1+u)e^{-u}$. Reuse its absolute convergence; no finite-tail
replacement is made. The elementary inequalities
$|E(u)|\le e^{|u|^2/2}$ and
$E(u)-1=-u^2\int_0^1s e^{-su}\,ds$ give

$$
|g_a(a+w)-1|
\le (\sqrt e-1)K_a|w|^2e^{K_a|w|^2/2}
\quad(w\in\mathbb C).
\tag{LC267}
$$

Indeed $s|u|\le(|u|^2+s^2)/2$ bounds the scalar remainder by
$(\sqrt e-1)|u|^2e^{|u|^2/2}$. Telescope finite products using the
bound on $|E|$, and then take their locally uniform limit.
Unlike the logarithm in (LC265), this estimate is valid even beyond
the initial zero-free disc, and so pays every arc of the exact circle.

For a positive integer $n$, put $k_a=|a|^2K_a/n$ and suppose $k_a<1$.
Apply (LC176) to the entire function $g_a$ and subtract its application
to $1$. With $c_n=n!e^n/n^n$ the complete circle gives

$$
\begin{aligned}
|\mathscr T_ng_a(a)-1|
&\le \frac{(\sqrt e-1)|a|^2K_ac_n}{\pi}
 \int_{-\pi}^{\pi}(1-\cos\theta)
 e^{-n(1-k_a)(1-\cos\theta)}\,d\theta\\
&\le C_{\rm fin}\frac{k_a}{(1-k_a)^{3/2}},\qquad
C_{\rm fin}=\frac{\pi^3(\sqrt e-1)e^{1/12}}8<3.
\end{aligned}
\tag{LC268}
$$

The last step uses
$2\theta^2/\pi^2\le1-\cos\theta\le\theta^2/2$ on this circle,
the classical Stirling upper bound $c_n\le\sqrt{2\pi n}e^{1/12}$,
and the full real Gaussian second moment. In particular $k_a\le1/16$
makes the error strictly less than $1/4$. The conclusion is uniform
for complex $a$ and retains the infinite original exterior product.

### Keep the exact drift and its nonzero amplitude

Set $d_n(a)=1-ab_a/n$ and $\Theta_n(a)=a/d_n(a)$ when $d_n(a)\ne0$.
The exponential-tilt identity (LC202), with the fixed scalar $b_a$
and entire remainder $g_a$ in place of its polynomial input, yields

$$
\mathscr T_nA(\Theta_n(a))
=A(a)e^{-ab_a}d_n(a)^{-n}(1+\epsilon_n(a)),\qquad
|\epsilon_n(a)|\le3\frac{k_a}{(1-k_a)^{3/2}}.
\tag{LC269}
$$

This substitution is an application of the same coefficient identity;
$b_a$ is held fixed inside each extraction. The large exponential
amplitude is retained exactly. For real $a$, $d_n(a)>0$ and
$k_a\le1/16$, the displayed ratio lies in $(3/4,5/4)$.
This is not a tangent-relative derivative comparison for the full source.

### Cover the actual target disc rather than only transported points

Let $C_b$ be a fixed original-source constant for
$|b_c|\le C_bL/D$ in (LC205), and let $C_{\rm abs}$ be the fixed
constant in (LC263). Take
$S=C_{\rm abs}+C_b+1$ and $C_*=32S$.
For every positive integer $n$ with $\nu\ge C_*L$, the consequence is

$$
\mathscr T_nA(t)\ne0\quad(|t-c|\le D/8),\qquad
\operatorname{sgn}\mathscr T_nA(t)=\operatorname{sgn}A(c)
\quad(t\in\mathbb R,\ |t-c|\le D/8).
\tag{LC270}
$$

Here is the source correspondence and coverage proof. On
$U=\{a:|a-c|\le D/4\}$, (LC263) gives
$K_a\le C_{\rm abs}L/D^2$. The complete differentiated product gives
$|b'_a|\le K_a$, and integration from $c$ shows
$|b_a|\le BL/D$ with $B=C_b+C_{\rm abs}/4\le S$.
With $e_0=D/(4c)=\rho/(4T)\le1/1024$, these imply

$$
k_a\le(1+e_0)^2\frac{C_{\rm abs}L}{\nu}<1/16,
\qquad
q:=\sup_U|ab_a/n|
\le\frac{(1+e_0)D}{32c}<1/4096,
\qquad
|\Theta_n(a)-a|
\le\frac{(1+e_0)^2B}{32S(1-q)}D<D/16.
\tag{LC271}
$$

The exterior clearance makes $A$ zero-free in a neighborhood of $U$;
the bound on $q$ does the same for $d_n$. Thus $\Theta_n$ is holomorphic
there, and (LC269) is nonzero at every image point.
For any actual target $|t-c|\le D/8$, on $\partial U$ one has
$|a-t|\ge D/8>|\Theta_n(a)-a|$. The classical Rouché theorem applied
to $(a-t)+(\Theta_n(a)-a)$ supplies exactly one preimage in the
interior of $U$, counting multiplicity. This proves the first part of
(LC270) at the actual target. For real $t$, reality of $A$ and uniqueness
make the preimage real. Its $d_n(a)>0$, and $A(a)$ has the sign of
$A(c)$ throughout the real diameter. The ratio following (LC269)
proves the sign assertion.

The degree condition is $n\ge C_*T^2\log(T+2)/\rho^2$, with constants
from the unchanged original source. It has no denominator involving
the initial spacing or any selected zero's derivative. The empty
selection $Q=1$ is also allowed: if the entire selected source disc
is zero-free, (LC270) certifies that $J=\mathscr T_nF$ is zero-free
on the actual smaller target disc.
The pole-removal bounds in (LC204)--(LC205) also hold for selections of
degree zero or one: their degree-at-least-two proviso concerns the
preceding cluster model, not the analytic pole-removal argument.

For a nonempty selection, (LC270) instead certifies only the extracted
complete exterior factor. Finite extraction does not commute with
factorization: $\mathscr T_n(AQ)$ is generally different from
$(\mathscr T_nA)(\mathscr T_nQ)$. Consequently this certificate alone
does not control the coupled selected roots, their actual-node responses
$J'(t)G(t)$ or the evolving exterior divisor of a heat flow. The
unpaid task is the joint finite extraction of that same $A$ and $Q$,
with all growing-multiplicity coupling terms retained. The local
critical-line premise also remains conditional. Original-source
all-node signs, RH and strict Robin for every integer $H>5040$ remain
unresolved.


## Complete exterior dual responses and the exact coupled recurrence

Retain the unchanged original source, every local critical-zero and
complete-removal premise of (LC263), and every parameter of
(LC267)--(LC271). Write $S=C_{\rm abs}+C_b+1$. The following is a
repo-derived analytical extension of the existing exterior certificate.
The canonical product, finite coefficient circle and exponential tilt
are reused. No global exterior real-root assumption, Lean verification
or originality certification is supplied.

### Two derivative operations remain distinct

For the complete centered product in (LC267), differentiation of finite
products and locally uniform convergence give

$$
|g_a'(a+w)|\le\sqrt e\,K_a|w|e^{K_a|w|^2/2}.
\tag{LC272}
$$

Indeed $E'(u)=-ue^{-u}$ and
$e^{-\Re u}\le\sqrt e\,e^{|u|^2/2}$. Each differentiated term is
bounded by $\sqrt e\,|w|\,|a-\zeta|^{-2}$ times the same complete
Gaussian product majorant. Summing the absolutely convergent mass
proves the estimate without a logarithmic derivative pole at a zero.

Use the same exact coefficient circle (LC176). Its elementary Stirling
bound gives $|\mathcal K_n(\theta)|\le e\sqrt n\,
 e^{-n(1-\cos\theta)}/(2\pi)$. Put
$\sigma_a=|a|/\sqrt n$ and $k_a=\sigma_a^2K_a<1$. The first and third
absolute Gaussian moments, with (LC272) and (LC267), respectively give

$$
\begin{aligned}
|\mathscr T_n(g_a')(a)|
 &\le\frac{4K_a\sigma_a}{1-k_a},\\
|(\mathscr T_ng_a)'(a)|
 &\le\frac{7K_a\sigma_a}{(1-k_a)^2}.
\end{aligned}
\tag{LC273}
$$

For the second line use the exact integration-by-parts identity

$$
(\mathscr T_ng_a)'(a)=\frac na
\int_{-\pi}^{\pi}\mathcal K_n(\theta)(1-e^{i\theta})
\bigl(g_a(ae^{i\theta})-1\bigr)\,d\theta.
$$

The constant function contribution vanishes. The Gaussian constants
are $e\pi\sqrt e/4<4$ and
$e\pi^3(\sqrt e-1)/8<7$. All points $a$ in the source disc are nonzero.
These are two different extraction responses, not a commutation of
$\mathscr T_n$ with differentiation.

Set
$H=\mathscr T_nA$, $V=\mathscr T_nA'$,
$\ell=H'/H$, $s=V/H$ and $v(t)=t^2/n$ wherever $H\ne0$.
For a fixed $a$, keep $b_a$ fixed inside the tilt, and let
$d_a=1-ab_a/n$, $t=\Theta_n(a)$ and
$\epsilon_a=\mathscr T_ng_a(a)-1$. The exact tilt gives

$$
\begin{aligned}
s(t)&=b_a+\frac{\mathscr T_n(g_a')(a)}{1+\epsilon_a},\\
\ell(t)&=d_ab_a+d_a^2
\frac{(\mathscr T_ng_a)'(a)}{1+\epsilon_a}.
\end{aligned}
\tag{LC274}
$$

The second line differentiates the fixed-tilt identity, whose argument
is $t/(1+b_at/n)$ and whose amplitude is $(1+b_at/n)^n$.
It does not differentiate a freely moving source normalization.
For $k_a\le1/16$, (LC268) makes $|\epsilon_a|<1/4$, so

$$
|s(t)-b_a|\le6K_a\sigma_a,\quad
|\ell(t)-d_ab_a|\le12|d_a|^2K_a\sigma_a,\quad
|\chi(t)-a|\le12K_a\sigma_a^3,
\qquad \chi(t)=t-v(t)\ell(t).
\tag{LC275}
$$

For the last bound, $t-v(t)d_ab_a=a$ and
$v(t)d_a^2=a^2/n$ cancel exactly. This retains the complete amplitude
and strengthens the transported-coordinate error to
$O(DL/\nu^{3/2})$ under the existing source mass bound.

### An explicit linear budget controls both local coefficients

For $\nu\ge32SL$, reuse the complex coverage in (LC270)--(LC271).
It supplies a source preimage $|a-c|<D/4$ for every
$|t-c|\le D/8$, with $k_a<1/16$, $|d_a|<2$,
$|b_a|\le(C_b+C_{\rm abs}/4)L/D$ and
$\sigma_a\le2D/\sqrt\nu$.
With the loose explicit constant $C_1=128S$, (LC274)--(LC275) imply

$$
\begin{aligned}
|\ell(t)|+|s(t)|&\le C_1L/D
&&(|t-c|\le D/8),\\
|\ell^{(m)}(t)|+|s^{(m)}(t)|
&\le C_1m!16^mL/D^{m+1}
&&(|t-c|\le D/16,\ m\ge0).
\end{aligned}
\tag{LC276}
$$

The functions are holomorphic because $H$ is nonzero on the outer
disc. Apply the Cauchy estimate to each function on a circle of radius
$D/16$; their combined bound is the displayed one.
These constants do not depend on selected degree or initial spacing.

Put $\eta(t)=1-v(t)s'(t)$ and increase the threshold to
$\nu\ge256C_1L=32768SL$. Since $|t|\le2c$ on the inner disc,
$v(t)\le4D^2/\nu$ on its real diameter. Equation (LC276) gives
$|\chi'-1|\le68C_1L/\nu$ and
$|\eta-1|\le64C_1L/\nu$. Consequently

$$
\frac12<\chi'(t)<\frac32,\qquad
\frac12<\eta(t)<\frac32,\qquad
|\chi(t)-t|\le4C_1DL/\nu
\quad(t\in\mathbb R,\ |t-c|\le D/16).
\tag{LC277}
$$

The degree requirement is the explicit conditional threshold
$n\ge32768S\,T^2\log(T+2)/\rho^2$. It retains the source constants;
no numerical instantiation of $C_{\rm abs}$ or $C_b$ is asserted.

### The full source remains a coupled, noncommutative problem

Absorb a nonzero real scalar into $A$ and write
$Q(z)=\prod_{j=1}^r(z-\alpha_j)$, with every multiplicity retained.
The coefficient rule
$(n)_{\underline{k+1}}n^{-k-1}=(1-k/n)(n)_{\underline k}n^{-k}$
gives the exact multiplication operator
$\mathfrak L_n=t-(t^2/n)\partial_t$. Thus, for the original full source,

$$
J=\mathscr T_n(AQ)=Q(\mathfrak L_n)H,\qquad
G=\mathscr T_n((AQ)')=Q'(\mathfrak L_n)H+Q(\mathfrak L_n)V.
$$

Here $G$ extracts the source derivative; it differs from $J'$.
Conjugating $\mathfrak L_n$ by $H$ gives
$\mathcal Bf=\chi f-vf'$. Starting from $P_0=1$, $S_0=0$, define

$$
\begin{aligned}
P_j&=(\mathcal B-\alpha_j)P_{j-1},\\
S_j&=(\mathcal B-\alpha_j)S_{j-1}+\eta P_{j-1}.
\end{aligned}
\qquad
J=HP_r,\quad G=H(sP_r+S_r).
\tag{LC278}
$$

To verify the second recursion, first set $R_0=s$ and
$R_j=P_{j-1}+(\mathcal B-\alpha_j)R_{j-1}$. Source differentiation
and exact multiplication give $G=HR_r$. Then $S_j=R_j-sP_j$ and
$[\mathcal B,M_s]=-vM_{s'}$ give precisely (LC278).
This algebra is an application of the unchanged multiplier, not a new
general convolution-preservation theorem.

At every real actual node in the $H$-nonvanishing disc,
$J(t)=0$ is equivalent to $P_r(t)=0$, and

$$
J'(t)G(t)=H(t)^2P_r'(t)S_r(t).
\tag{LC279}
$$

No simplicity is assumed in this identity. At a multiple node the
right-hand side vanishes; strict positivity would also have to exclude
that case. The positive coefficients in (LC277) do not prove positivity
of $P_r'S_r$ after all $r\le C_0L$ steps. Already
$S_1=\eta$ and
$S_2=\eta(2\chi-\alpha_1-\alpha_2)-v\eta'$ expose a derivative term
with unpaid sign and slope comparison. Higher steps retain further
noncommuting derivatives.

There is also a boundary obligation: the selected source zeros have
$\alpha_j=(T+\delta_j)^2$, $|\delta_j|\le4\rho$, so only
$|\alpha_j-c|\le8D+16\rho^2$ follows. They need not all lie in the
$D/8$ exterior nonvanishing disc. A complete interlacing root chain
inside the smaller interval cannot be assumed. What remains missing
is a uniform high-order sign and boundary estimate for this exact
coupled recurrence on the actual original source. The local
all-critical premise, all-height exclusion, RH and strict Robin for
all integers $H>5040$ remain unresolved.


## Joint source response and a gap-free two-zero application

Retain the original source, every conditional local-critical and complete-removal
premise in (LC263), all exterior zeros in $A$, and the fixed constants and
parameters of (LC267)--(LC279). Set $R=C_1L$, $C_1=128S$ and
$M_R=32R+R^2/2$. The additional bounds below are ordinary analytical
applications of the existing finite multiplier and (LC276), not new
factorization, degree-lowering or root-preservation theorems. They have
no Lean certification or originality certification.

### The two responses inherit an exact linkage

For $H=\mathscr T_nA$ and $V=\mathscr T_nA'$, the same falling-factorial
coefficient rule gives

$$
H'=V-\frac tnV',\qquad
\ell-s=-\frac tn(s'+s\ell).
\tag{LC280}
$$

This is a reused multiplier identity. In particular, the coefficient of
$t^n$ in $V-(t/n)V'$ cancels; no missing top-degree term is discarded.
It is also the normalization mechanism of the universal degree-lowering
supplier in `Blueprint/D5/S3/Zeros/Jensen/NormalizedJensenDegreeLowering.md`.
The source-specific estimate comes from combining that linkage with the
complete exterior response bound, rather than treating $\ell$ and $s$
as unrelated functions. Since $1/n=D^2/(\nu c^2)$ and $|t|\le2c$,
(LC276) and $|s\ell|\le(|s|+|\ell|)^2/4$ give

$$
\begin{aligned}
|\ell-s|&\le\frac{M_R}{\nu c}
&&(|t-c|\le D/16),\\
|(\ell-s)'|&\le\frac{32M_R}{\nu cD}
&&(|t-c|\le D/32).
\end{aligned}
\tag{LC281}
$$

Both are complex-disc estimates. The second applies Cauchy's estimate
on a circle of radius $D/32$ inside the first disc. Consequently

$$
\begin{aligned}
\eta-\chi'&=v'\ell+v(\ell-s)',\\
|\eta-\chi'|&\le\frac Dc
 \left(\frac{4R}{\nu}+\frac{128M_R}{\nu^2}\right)
 <\frac{D}{32c}=\frac{\rho}{32T}
\quad(|t-c|\le D/32,\ \nu\ge256R).
\end{aligned}
\tag{LC282}
$$

For the strict inequality, $R=128S\log(T+2)>384$ and
$4R/\nu+128M_R/\nu^2\le1/64+1/(16R)+1/1024<1/32$.
The constants $C_{\rm abs},C_b$ remain fixed source constants without a
numerical instantiation. This is a stronger joint bound than separately
estimating $|\chi'-1|$ and $|\eta-1|$ by $O(R/\nu)$.

### The derivative discrepancy retains a separate forcing term

For the unchanged recurrence (LC278), put $W_j=S_j-P_j'$. Differentiating
its first equation and subtracting gives the exact bookkeeping

$$
W_j=(\mathcal B-\alpha_j)W_{j-1}
       +v'P_{j-1}'+(\eta-\chi')P_{j-1},\qquad W_0=0.
\tag{LC283}
$$

This identity is reuse, not a propagation estimate. In particular,
$|v'|\le4\rho^2/\nu$ has no additional $1/T$ factor. A small coefficient
in (LC282) does not bound $W_r/P_r'$ at a node with a small slope.

### A core of at most two zeros permits growing total selection

Let the unchanged full selection have $r\le C_0L$ factors and put
$q=\#\{j:|\alpha_j-c|\le D\}$, counting every multiplicity.
Assume only $q\le2$ in addition to the existing conditional source
premises. The total selected degree $r$ may still grow; the new
restriction is on its central core, not on its distant selected roots.
Factor $Q=Q_{\rm core}Q_{\rm far}$ inside the proof and set
$\widehat A=AQ_{\rm far}=F/Q_{\rm core}$.
This auxiliary regrouping leaves the original $F,Q,P_r,S_r,J,G$
unchanged. No multiplicativity of $\mathscr T_n$ is used.

For $|a-c|\le D/4$, every added far root has $|a-\alpha_j|>3D/4$.
The complete product mass and central drift therefore obey

$$
K_{\widehat A}(a)\le(C_{\rm abs}+2C_0)\frac L{D^2},\qquad
\left|\frac{\widehat A'}{\widehat A}(c)\right|
 \le(C_b+C_0)\frac LD.
\tag{LC284}
$$

All original infinite exterior zeros and the actual far selected factors
remain in $\widehat A$. It is nonzero throughout this working disc.
Thus the full-product and coefficient-circle proofs in (LC267)--(LC277)
apply with $S_*=S+3C_0$, $E=128S_*L$ and the stronger threshold

$$
\nu\ge256E=32768(S+3C_0)L.
\tag{LC285}
$$

This reapplies their analytic inputs; it does not claim that removing
only the core meets the original definition of a complete selection.
In particular, $\widehat H=\mathscr T_n\widehat A$ is nonzero on
$|t-c|\le D/8$. Define $\widehat\ell,\widehat s,\widehat\chi,
\widehat\eta$ exactly as in (LC274)--(LC277), with $\widehat A$ replacing
$A$. Their complex derivative bounds use $E$ in place of $R$.

### The quadratic core has a forced nonzero node amplitude

In the complex disc $\mathcal D=\{|t-c|\le D/16\}$ those bounds give

$$
|\widehat\chi''|,\ |\widehat\eta'|
 <\frac{2200E}{\nu D}.
\tag{LC286}
$$

Indeed $\widehat\chi''=-v''\widehat\ell-2v'\widehat\ell'
-v\widehat\ell''$ and
$\widehat\eta'=-v'\widehat s'-v\widehat s''$.
Use $|v|\le4D^2/\nu$, $|v'|\le4D/\nu$, $|v''|\le2/\nu$ and (LC276);
the resulting constants are $2178$ and $2112$, respectively.
On the real diameter $I=[c-D/16,c+D/16]$, put
$U=v\widehat\chi'>0$. Since $v'/\sqrt v=2/\sqrt n$, (LC286) gives

$$
\frac{|U'|}{\sqrt v}\le\frac3{\sqrt n}
 +\frac{4400E}{\nu^{3/2}}<\frac18,\qquad
\frac{|v\widehat\eta'|}{\sqrt v}
 <\frac{4400E}{\nu^{3/2}}<\frac18.
\tag{LC287}
$$

Here $E>384$, $\nu\ge256E$, $n\ge\nu$ and $\sqrt\nu>256$;
$(6+4400/256)/256<1/8$ already bounds the larger complex comparison
used below. No sign of $\widehat\eta'$ is imposed.

When $q=2$, write its two real roots as $a_1,a_2$, allowing equality,
and set $m=(a_1+a_2)/2$, $\delta=(a_1-a_2)/2$ and
$x=\widehat\chi-m$. Apply the exact coupled recurrence only to this
auxiliary core, writing its responses as $p_q,w_q$. Thus the same full
source has $J=\widehat Hp_q$ and
$G=\widehat H(\widehat sp_q+w_q)$. For $q=2$,

$$
p_2=x^2-\delta^2-U,\qquad
p_2'=2x\widehat\chi'-U',\qquad
w_2=2\widehat\eta x-v\widehat\eta'.
\tag{LC288}
$$

At every real actual node, $x^2=\delta^2+v\widehat\chi'\ge v/2$,
so $x\ne0$. Equation (LC287) bounds both derivative errors by
$\sqrt2|x|/8<|x|/4$, while both leading terms have magnitude greater
than $|x|$. The two responses consequently have the sign of $x$ and
magnitude greater than $3|x|/4$. Returning to the original responses,

$$
P_r'(t)S_r(t)>\frac14
 \left(\frac{\widehat H(t)}{H(t)}\right)^2
 \begin{cases}
 1,&q=1,\\
 v(t),&q=2,
 \end{cases}
\quad(t\in I,\ J(t)=0).
\tag{LC289}
$$

For $q=1$, use $p_1=\widehat\chi-a_1$ and $w_1=\widehat\eta$.
For $q=2$, $p_2'w_2>x^2/2\ge v/4$. In both cases the exact equality
$H^2P_r'S_r=J'G=\widehat H^2p_q'w_q$ proves (LC289), retaining the
complete nonzero source amplitude. Every such node is simple. For
$q=0$, $J=\widehat H$ has no node in the disc.

### The entire inner complex disc has at most two real simple zeros

This assertion does not presume that the actual nodes are already real.
For $q=2$, put $\sigma_0=c/\sqrt n=D/\sqrt\nu$. Throughout $\mathcal D$,
$|t/c-1|\le1/4096$, so

$$
\left|\frac v{\sigma_0^2}-1\right|<\frac1{1024},\qquad
|\widehat\chi'-1|\le\frac{17}{64},\qquad
\left|\frac U{\sigma_0^2}-1\right|<\frac12.
\tag{LC290}
$$

In particular $\Re U>\sigma_0^2/2$. The analytic square root
$R_2(t)=\sqrt{\delta^2+U(t)}$, positive on the real diameter,
satisfies $|R_2|>\sigma_0/\sqrt2$. Here $|v|<2\sigma_0^2$ and (LC286)
give $|U'|/\sigma_0\le6/\sqrt n+4400E/\nu^{3/2}<1/8$.
Consequently $|R_2'|<1/8$. The two analytic branches

$$
f_+=\widehat\chi-m-R_2,\qquad
f_-=\widehat\chi-m+R_2,
\qquad p_2=f_+f_-,\qquad
|f_\pm'-1|<\frac12
\tag{LC291}
$$

are each injective: integrate their derivative difference along the
line segment between any two points of the convex disc. They each
preserve complex conjugation. A nonreal zero would therefore produce
two zeros of the same injective branch. Their zeros cannot coincide,
since $R_2\ne0$, and their derivatives do not vanish. It follows that
$\mathcal D$, including its boundary, contains at most two zeros of
$J$, all real and simple. At $q=1$, the same argument applies to
$\widehat\chi-a_1$; at $q=0$, nonvanishing was already established.

Let $t_\pm=c\pm D/16$. Since each branch is strictly increasing on $I$,
its complete node-existence criterion is

$$
f_\pm(t_-)\le0\le f_\pm(t_+).
\tag{LC292}
$$

Each satisfied branch criterion gives exactly one node. No complete
interlacing chain or membership of all selected source roots in $I$
is assumed. For $q=2$, the upper and lower branch nodes, when present,
lie within $\Delta=4ED/\nu+\sqrt6D/\sqrt\nu$ of
$a_{\max}=m+|\delta|$ and $a_{\min}=m-|\delta|$, respectively.
This follows from $|\widehat\chi-t|\le4ED/\nu$ and
$0\le R_2-|\delta|\le\sqrt U\le\sqrt6D/\sqrt\nu$ on the real diameter.
Containment of the corresponding closed $\Delta$-neighborhood in $I$
is a sufficient node-existence condition, as direct endpoint evaluation
of (LC291) shows.

The core regrouping and node-sign application use the individual
derivative bounds in (LC276); they do not assert that (LC282) alone
proves positivity. They allow growing total selection and retain every
actual exterior factor, but require central total multiplicity $q\le2$.
Removing that restriction, controlling arbitrary growing-core nodes
and their boundary crossings, and discharging the local all-critical
premise remain unpaid. RH and strict Robin for every integer $H>5040$
remain unresolved.


## Three core zeros at a fixed linear logarithmic budget

Retain the same original $F(z)=\Xi(\sqrt z)/\xi(1/2)$, multiplier,
$J,G,H,P_r,S_r$, and every local-critical and complete-removal premise
in (LC263). In particular, every actual source zero, with multiplicity,
in the closed radius-$4\rho$ disc centered at $1/2+iT$ is assumed
critical and removed in the full $Q$. The complete exterior $A=F/Q$
retains every other zero, possibly nonreal. Keep $T\ge32$,
$L=\log(T+2)$, $0<\rho\le1/8$, $c=T^2$, $D=T\rho$,
$\nu=n\rho^2/T^2$ and $r\le C_0L$, with positive integer $n$.

Reuse the regrouping $Q=Q_{\rm core}Q_{\rm far}$ and
$\widehat A=AQ_{\rm far}$ from (LC284). Its mass and drift estimates
use the far-root distances and total count, without a $q\le2$
restriction. Thus the zero-free $\widehat H=\mathscr T_n\widehat A$
and complete exterior jets in (LC276)--(LC277) apply to a core of
three, with $E=128(S+3C_0)L$ and $S=C_{\rm abs}+C_b+1$.
Removing only the core is not asserted to satisfy the original
complete-removal premise. No multiplicativity of $\mathscr T_n$
is used, and no exterior factor or theta tail is discarded.

Assume the core count, including multiplicity, is exactly $q=3$.
Write its actual real roots as $\alpha_1,\alpha_2,\alpha_3$, each
with $|\alpha_i-c|\le D$. Put

$$
\begin{gathered}
\mathcal D=\{t\in\mathbb C:|t-c|\le D/16\},\qquad
I=[t_-,t_+],\quad t_\pm=c\pm D/16,\\
\sigma=c/\sqrt n=D/\sqrt\nu,\qquad
\nu\ge8192E=2^{20}(S+3C_0)L.
\end{gathered}
\tag{LC293}
$$

Under these conditional inputs, every $J$-zero in the closed
$\mathcal D$ is real and simple, and there are at most three.
Every actual node satisfies the original-response bound
$P_r'S_r>(\widehat H/H)^2v^2/4$, where $v(t)=t^2/n$.
The argument below supplies the joint amplitude, complex branches
and endpoint criteria. This is an ordinary analytical application;
no Lean verification or originality certification is supplied.

### The exact cubic retains both complete exterior responses

Use hats throughout for the auxiliary complete exterior quantities.
Define

$$
\begin{gathered}
m=(\alpha_1+\alpha_2+\alpha_3)/3,\qquad \beta_i=\alpha_i-m,\\
a=\frac16\sum_{i=1}^3\beta_i^2,\qquad b=\beta_1\beta_2\beta_3,\\
Q_{\rm core}(m+z)=z^3-3az-b,\qquad
 a\ge0,\quad |b|\le2a^{3/2},\\
x=\widehat\chi-m,\qquad U=v\widehat\chi',\qquad
V_3=vU',\qquad Z_3=v(v\widehat\eta')',\qquad
M_3=3(x^2-a-U).
\end{gathered}
\tag{LC294}
$$

The invariant inequality follows from the real-source discriminant
$108a^3-27b^2=\prod_{i<j}(\beta_i-\beta_j)^2\ge0$.
Source roots may coincide, including an initial triple root.
For the same exact recurrence (LC278), use auxiliary responses
$p_3,w_3$ so that $J=\widehat Hp_3$ and
$G=\widehat H(\widehat s p_3+w_3)$. Applying
$\mathcal C=x-v\partial_t$ gives
$\mathcal C^21=x^2-U$ and
$\mathcal C^31=x^3-3Ux+vU'$. The coupled recurrence therefore gives

$$
\begin{aligned}
p_3&=x^3-3(a+U)x-b+V_3,\\
p_3'&=\widehat\chi'M_3-3U'x+V_3',\\
w_3&=\widehat\eta M_3-3v\widehat\eta'x+Z_3.
\end{aligned}
\tag{LC295}
$$

In particular $Z_3=vv'\widehat\eta'+v^2\widehat\eta''$.
All noncommuting derivative terms remain present. The polynomial
in an independent variable $z$ with these coefficients will be used
for comparison; $p_3$ is not asserted to be a cubic polynomial in $t$.

### A uniform complex jet budget

Put $\epsilon=E/\nu\le1/8192$. On the full closed $\mathcal D$,
reuse (LC276), with $E$ replacing $C_1L$, and (LC286). They give
$|\widehat\chi'-1|\le68\epsilon$,
$|\widehat\eta-1|\le64\epsilon$ and
$\max\{|\widehat\chi''|,|\widehat\eta'|\}<2200\epsilon/D$.
For one further derivative use
$\widehat\chi'''=-3v''\widehat\ell'-3v'\widehat\ell''-v\widehat\ell'''$
and
$\widehat\eta''=-v''\widehat s'-2v'\widehat s''-v\widehat s'''$.
The $m=1,2,3$ constants from (LC276) give respectively $104544$ and
$102432$, so

$$
\max\{|\widehat\chi'''|,|\widehat\eta''|\}
 <110000\epsilon/D^2.
\tag{LC296}
$$

Since $D/c=\rho/T\le1/256$ and $|t/c-1|\le1/4096$, we have
$|v/\sigma^2-1|<1/1024$,
$|v|\le2\sigma^2$, $|v'|\le3\sigma^2/D$ and
$|v''|\le2\sigma^2/D^2$. Product differentiation consequently gives

$$
\begin{aligned}
|U'|&\le6\sigma^2/D,& |U''|&\le32\sigma^2/D^2,\\
|V_3|&\le12\sigma^4/D,& |V_3'|&\le82\sigma^4/D^2,\\
|v\widehat\eta'|&\le\sigma^2/D,& |Z_3|&\le56\sigma^4/D^2.
\end{aligned}
\tag{LC297}
$$

For example the $U''$ coefficient is bounded by
$3+233200\epsilon<32$, while the $Z_3$ coefficient is
$453200\epsilon<56$. Here $S+3C_0>1$ and $L>3$ imply $E>384$,
so $\nu>8192\cdot384$. The estimates actually needed below are

$$
\begin{gathered}
|U-\sigma^2|<\sigma^2/32,\qquad |V_3|<\sigma^3/32,\\
\max\left\{\frac{|U'|}{\sigma},
\frac{|V_3'|}{\sigma^2},\frac{|v\widehat\eta'|}{\sigma},
\frac{|Z_3|}{\sigma^2}\right\}<1/256,\\
|\widehat\chi'-1|<1/64,\qquad |\widehat\eta-1|\le1/128.
\end{gathered}
\tag{LC298}
$$

These hold on $D/16$ directly from the individual jets. No joint
mismatch estimate confined to the smaller $D/32$ disc is used.

### A cubic amplitude estimate and the original node margin

The following elementary comparison controls repeated initial roots.
For $a\ge0$, $|b|\le2a^{3/2}$, $u>0$, $e\in\mathbb R$ with
$|e|\le u^{3/2}$, set
$C(z)=z^3-3(a+u)z-b+e$ and $h=\sqrt{a+u}$.
Since $h^3-a^{3/2}=uh+a(h-\sqrt a)\ge uh$,
$2h^3-|b-e|\ge2uh-u^{3/2}\ge uh>0$.
Signs at $-2h,-h,h,2h$ put one distinct real root in each of
$(-2h,-h)$, $(-h,h)$ and $(h,2h)$.
For any root $\lambda$, put $y=|\lambda|\le2h$. Its equation gives
$(y-h)^2(y+2h)\ge2h^3-|b-e|\ge uh$.
Thus $|y-h|\ge\sqrt u/2$. Adjacent roots have gap at least $\sqrt u$,
and

$$
|C'(\lambda)|\ge\frac32\sqrt u\,(|\lambda|+h)
 \ge\frac32u.
\tag{LC299}
$$

At a real actual node $t\in I$, $p_3(t)=0$ and (LC298) gives
$U>\sigma^2/2$ and $|V_3|<U^{3/2}$. Apply (LC299) with
$u=U,e=V_3$ at the root $x(t)$.
It yields $|x|/|M_3|<1/\sigma$ and $1/|M_3|<2/\sigma^2$.
Using (LC295) and (LC298), each of
$|(p_3'-\widehat\chi'M_3)/M_3|$ and
$|(w_3-\widehat\eta M_3)/M_3|$ is less than $5/256$.
Both real ratios $p_3'/M_3$ and $w_3/M_3$ exceed $1/2$.
Since $U=v\widehat\chi'>3v/4$ on $I$, the same original-node
identity (LC279) gives

$$
\begin{gathered}
p_3'w_3>\frac14M_3^2\ge\frac9{16}U^2
 >\frac{81}{256}v^2>\frac14v^2,\\
H^2P_r'S_r=J'G=\widehat H^{\,2}p_3'w_3,\qquad
P_r'S_r>\frac14\left(\frac{\widehat H}{H}\right)^2v^2>0.
\end{gathered}
\tag{LC300}
$$

Both nonzero amplitudes are real on $I$, so the returned margin
retains their squared ratio. This proves a relative node bound;
positivity of $\widehat\chi'$ and $\widehat\eta$ alone is insufficient.

### Complex branches on the entire closed target disc

Define $C_t(z)=z^3-3(a+U(t))z-b+V_3(t)$ and the fixed
$C_*(z)=z^3-3(a+\sigma^2)z-b$.
The latter has distinct real roots
$\lambda_1^0<\lambda_2^0<\lambda_3^0$, with gaps at least $\sigma$,
by (LC299). Put $h_0=\sqrt{a+\sigma^2}$.
On each fixed circle $|z-\lambda_j^0|=\sigma/8$,

$$
\begin{aligned}
|C_*(z)|&\ge\frac{\sigma}{8}\left(\frac78\right)^2
 |C_*'(\lambda_j^0)|
 \ge\frac{147}{1024}\sigma^2(|\lambda_j^0|+h_0),\\
|C_t(z)-C_*(z)|&\le3|U-\sigma^2||z|+|V_3|
 <\frac3{32}\sigma^2(|\lambda_j^0|+h_0)
 <|C_*(z)|.
\end{aligned}
\tag{LC301}
$$

For the perturbation bound use $|z|\le|\lambda_j^0|+\sigma/8$
and $h_0\ge\sigma$. Rouché gives exactly one simple moving root
$\lambda_j(t)$ in each fixed disc, for every $t\in\mathcal D$.
The roots have analytic labels on a neighborhood of the closed
parameter disc and preserve conjugation by uniqueness. In particular
$|\lambda_j(t)-\lambda_j^0|<\sigma/8$.
Each pairwise distance loses at most $\sigma/4$, giving
$|\partial_z C_t(\lambda_j)|\ge(9/16)|C_*'(\lambda_j^0)|$.
Implicit differentiation, rather than a Cauchy estimate on a smaller
disc, now gives

$$
\begin{gathered}
\lambda_j'=\frac{3U'\lambda_j-V_3'}{3(\lambda_j^2-a-U)},\qquad
|\lambda_j'|\le\frac{32}{9}\frac{|U'|}{\sigma}
 +\frac{32}{27}\frac{|V_3'|}{\sigma^2}
 <\frac1{54}<\frac1{32},\\
f_j(t)=\widehat\chi(t)-m-\lambda_j(t),\qquad
p_3=f_1f_2f_3,\quad J=\widehat Hf_1f_2f_3,\qquad
|f_j'-1|<\frac3{64}<\frac12.
\end{gathered}
\tag{LC302}
$$

Here $|\lambda_j|\le|\lambda_j^0|+\sigma/8
\le|\lambda_j^0|+h_0$ pays the numerator bound.
Line-segment integration in the convex closed $\mathcal D$ gives
$|f_j(t)-f_j(u)-(t-u)|\le(3/64)|t-u|$, so each branch is injective.
A nonreal zero would supply its distinct conjugate in the same branch,
contradicting injectivity. Branches cannot share a node because their
$\lambda_j(t)$ lie in disjoint fixed discs. The derivative bound and
zero-free $\widehat H$ imply simplicity, also at the target boundary.
This proves realness and at most three actual nodes on all of
$\mathcal D$, without deducing it merely from the reference cubic.

On $I$ each branch is real and strictly increasing, so its exact
existence criterion, including endpoint equality, and localization are

$$
\begin{gathered}
f_j(t_-)\le0\le f_j(t_+),\qquad
N_J(\mathcal D)=\sum_{j=1}^3
\mathbf1_{\{f_j(t_-)\le0\le f_j(t_+)\}},\\
b_j^*=m+\lambda_j^0,\qquad
\Delta_3=4ED/\nu+\sigma/8,\qquad
|f_j(t)-(t-b_j^*)|\le\Delta_3\quad(t\in I).
\end{gathered}
\tag{LC303}
$$

Every existing branch node lies within $\Delta_3$ of $b_j^*$.
Containment of $[b_j^*-\Delta_3,b_j^*+\Delta_3]$ in $I$ is sufficient
for existence; it is not a necessary condition. No three-node
existence, complete interlacing chain or membership of all original
selected roots in the target interval is asserted.

### Reused comparison and remaining interfaces

Nakano, Trinh and Wang, [*Beta Ensembles in the Freezing Regime and
Finite Free Convolutions*, arXiv:2603.01356v1](https://arxiv.org/html/2603.01356v1),
Theorem 3.1 and Lemma 3.9, supply the fixed finite-$N$ Hermite
finite-free comparison with real ordered initial data, allowing repeats.
For $N=3$, initial roots $\beta_i$ and time $\tau=\sigma^2$, their
probabilist-Hermite normalization identifies
$e^{-(\sigma^2/2)\partial_z^2}(z^3-3az-b)=C_*(z)$.
This finite comparison is reused literature, not a theorem for the
complete $J,G$ pair or its possibly nonreal infinite exterior.
The complete-source perturbation, joint amplitude and branch-speed
estimates above supply that restricted application interface.

The arbitrary-multiplicity real-node sign at the larger polynomial
budget (LC218) is also reused. The application here concerns a fixed
linear logarithmic $\nu$ budget with complex-node and boundary control.
At the stronger threshold (LC293), combine this three-core result with
(LC289)--(LC292) for $q\le2$: there are at most $q$ target nodes, all
real and simple, and for $1\le q\le3$ the node margin is
$P_r'S_r>(\widehat H/H)^2v^{q-1}/4$.
Repeated core roots are allowed subject to $q\le3$, while the total
selected multiplicity may grow to $C_0L$.

The fixed source constants remain numerically uninstantiated.
Uniform growing-core estimates for $q\le C_0L$ at $\nu=C_*L$, their
complex branches and boundary crossings, and discharge of the local
all-critical premise remain unresolved. No FIB ATOM bridge to these
signed complete-source estimates is supplied. RH and strict Robin
for every integer $H>5040$ remain unproved.

## Complete dual kernels and a shared root-response transport

Retain the original source, local all-critical and complete-removal
premises of (LC263), and the regrouping (LC284). In particular, every
exterior zero and every far selected factor remains in
$\widehat A=AQ_{\rm far}=F/Q_{\rm core}$. Retain total selected
multiplicity $r\le C_0L$, with $q\le r$. The core polynomial is monic,
of degree $q$, with real roots $\alpha_j$ satisfying
$|\alpha_j-c|\le D$; repeated core roots are allowed. Use
$E=128(S+3C_0)L$ and the complete auxiliary functions
$\widehat H,\widehat\ell,\widehat s,\widehat\chi,\widehat\eta$ from
(LC276)--(LC286), with $E$ replacing $C_1L$. Here
$\widehat H=\mathscr T_n\widehat A$,
$\widehat\ell=\widehat H'/\widehat H$,
$\widehat s=\mathscr T_n(\widehat A')/\widehat H$,
$v=t^2/n$, $\widehat\chi=t-v\widehat\ell$ and
$\widehat\eta=1-v\widehat s'$. Write
$\mathcal D=\{|t-c|\le D/16\}$ and
$I=[t_-,t_+]=[c-D/16,c+D/16]$.

This is a repo-derived analytical application of existing extraction
and finite-free suppliers, without Lean or originality certification.
The exact representation below does not certify its kernels' root
geometry or signed residues at growing degree. Those are separate
conditions, stated explicitly below.

### Literature suppliers and the coefficient convention

Martínez-Finkelshtein, Morales and Perales,
[*Real roots of hypergeometric polynomials via finite free convolution*,
arXiv:2309.10970v2](https://arxiv.org/html/2309.10970v2), Definition 2.5,
Propositions 2.11 and 2.13, supply the additive coefficient convention,
oriented interlacing and mesh preservation. Marcus, Spielman and
Srivastava, [*Finite free convolutions of polynomials*,
arXiv:1504.00350](https://arxiv.org/pdf/1504.00350), Definition 1.1
and Theorem 2.11, supply the same normalization and permutation average.
Sinclair, [*Finite free convolution via reproducing kernels and
squarefree algebras*, arXiv:2606.10870v2](https://arxiv.org/html/2606.10870v2),
Lemma 3.8, Proposition 3.9 and Corollary 3.11, connect the kernel pairing,
polarization and the classical Grace--Walsh--Szegő interface.

Throughout this application the convention, including lower-degree
arguments, is

$$
(P\boxplus_q R)(z)=\frac1{q!}\sum_{k=0}^q
 P^{(k)}(z)R^{(q-k)}(0).
\tag{LC304}
$$

This is the descending-coefficient convention of the first two
suppliers. Sinclair's ascending convention is used only through its
symmetric multiaffine polarization interface, not by identifying its
convolution symbol with (LC304). These general literature theorems are
reused, rather than reproved or counted as new source results.

### Generate both kernels from the same complete factor

For a holomorphic germ at $u=0$, set

$$
\begin{aligned}
\psi_t(u)&=\frac{t}{1+tu/n},&
K_t(u)&=(1+tu/n)^n\frac{\widehat H(\psi_t(u))}{\widehat H(t)},\\
M_t(u)&=e^{-\widehat\chi(t)u}K_t(u),&
b_t(u)&=u+\widehat s(\psi_t(u))-\widehat s(t),\qquad
N_t(u)=M_t(u)b_t(u),\\
M_t(u)&=\sum_{k\ge0}a_k(t)\frac{u^k}{k!},&
N_t(u)&=\sum_{k\ge0}d_k(t)\frac{u^k}{k!}.
\end{aligned}
\tag{LC305}
$$

In particular $a_0=1,a_1=0,d_0=0,d_1=\widehat\eta$.
Define a monic value kernel and a lower-degree response kernel by

$$
\begin{gathered}
R_{q,t}(z)=\sum_{k=0}^q\binom qk a_k(t)z^{q-k},\qquad
U_{q,t}(z)=\sum_{k=0}^q\binom qk d_k(t)z^{q-k},\\
\overline Q(z)=Q_{\rm core}(c+z),\qquad x(t)=\widehat\chi(t)-c,\\
C_t=\overline Q\boxplus_q R_{q,t},\qquad
W_t=\overline Q\boxplus_q U_{q,t},\qquad
C_t=\sum_{k=0}^q\frac{a_k}{k!}\overline Q^{(k)},\quad
W_t=\sum_{k=0}^q\frac{d_k}{k!}\overline Q^{(k)}.
\end{gathered}
\tag{LC306}
$$

Apply the exact exponential-tilt identity (LC202) to $\widehat A$
and to its source derivative. It gives, with the same $K_t$,

$$
\frac{\mathscr T_n(e^{uz}\widehat A)(t)}{\widehat H(t)}=K_t(u),
\qquad
\frac{\mathscr T_n((e^{uz}\widehat A)')(t)}{\widehat H(t)}
 =K_t(u)[u+\widehat s(\psi_t(u))].
\tag{LC307}
$$

Subtract $\widehat s(t)$ times the first identity from the second,
then apply $Q_{\rm core}(\partial_u)|_{u=0}$. The exact auxiliary
recurrences (LC278), now for the core, consequently have the representation

$$
\begin{gathered}
p_q(t)=C_t(x(t)),\qquad w_q(t)=W_t(x(t)),\\
J=\widehat H C_t(x),\qquad
G=\widehat H[\widehat s C_t(x)+W_t(x)].
\end{gathered}
\tag{LC308}
$$

This applies the existing tilt to both responses. The kernel is an
operator-symbol encoding; it does not replace the actual core by a
fictional repeated-root source or discard any exterior contribution.

### A common nonnegative weight transfers speed and response

Fix real $t\in I$ and suppose $R_{q,t}$ has simple real roots
$\beta_1<\cdots<\beta_q$. For $q\ge2$, mesh preservation makes
$C_t$ simple real-rooted even when $\overline Q$ has repeated roots.
The degree-one case follows directly from (LC304). Denote its ordered
roots by $\lambda_1<\cdots<\lambda_q$, and set

$$
R_{t,j}(z)=\frac{R_{q,t}(z)}{z-\beta_j},\qquad
\omega_{ij}=\frac{(\overline Q\boxplus_q R_{t,j})(\lambda_i)}
 {\partial_zC_t(\lambda_i)},\qquad
\gamma_j=\frac{U_{q,t}(\beta_j)}{\partial_zR_{q,t}(\beta_j)}.
\tag{LC309}
$$

Moving just one kernel root a sufficiently small positive distance
gives an oriented interlacing pair. Preservation of that orientation
implies that no ordered output root moves left. Implicit differentiation
identifies $\omega_{ij}=\partial\lambda_i/\partial\beta_j\ge0$.
Simultaneous translation gives the row sums; differentiating the sum
of output roots, which is the sum of the two input root sums, gives
the column sums. Linearity applied to
$U_{q,t}=\sum_j\gamma_jR_{t,j}$ then gives

$$
\begin{gathered}
\omega_{ij}\ge0,\qquad \sum_j\omega_{ij}=1,\qquad
\sum_i\omega_{ij}=1,\\
\lambda_i'=\sum_j\omega_{ij}\beta_j',\qquad
\frac{W_t(\lambda_i)}{\partial_zC_t(\lambda_i)}
 =\sum_j\omega_{ij}\gamma_j.
\end{gathered}
\tag{LC310}
$$

Here derivatives in $t$ use local analytic root labels. At an actual
node $x(t)=\lambda_i(t)$, put
$\delta_j=\widehat\chi'-\beta_j'$. The same weights occur in both
node amplitudes:

$$
p_q'=\partial_zC_t(\lambda_i)\sum_j\omega_{ij}\delta_j,
\qquad
w_q=\partial_zC_t(\lambda_i)\sum_j\omega_{ij}\gamma_j.
\tag{LC311}
$$

If all $\delta_j>0$, define
$\widetilde\omega_{ij}=\omega_{ij}\delta_j/
\sum_k\omega_{ik}\delta_k$. These weights are nonnegative with row
sum one, and the original complete response ratio is

$$
\frac{G(t)}{J'(t)}=\frac{w_q(t)}{p_q'(t)}
 =\sum_j\widetilde\omega_{ij}\frac{\gamma_j}{\delta_j},\qquad
\min_j\frac{\gamma_j}{\delta_j}\le\frac{G(t)}{J'(t)}
 \le\max_j\frac{\gamma_j}{\delta_j}.
\tag{LC312}
$$

Thus this transmission introduces no degree factor or division by a
separately estimated minimal actual-node slope. The missing signed
information has moved to the actual complete kernels, rather than
being supplied by the convex-combination formula.

### The precise kernel conditions still required

At $\nu\ge512E$, the complete jets already give

$$
|\widehat\chi'-1|\le68E/\nu<1/4,\qquad
|\widehat\eta-1|\le64E/\nu\le1/8
\quad(t\in\mathcal D).
\tag{LC313}
$$

For each growing degree under consideration, require the following
additional certificate, denoted $\mathsf K$:

* for every real $t\in I$, $R_{q,t}$ has $q$ simple real roots;
* for every complex $t\in\mathcal D$ and every root $\beta$ of $R_{q,t}$,
  $|\Im\beta|\le|\Im t|/4$;
* at every real $t\in I$, every residue $\gamma_j$ in (LC309) is strictly
  positive.

No quantitative mesh lower bound or degree-independent residue floor
is assumed here. None of these growing-degree conditions has been
established for the actual source by the preceding jets.

For any complex parameter, the permutation formula identifies $C_t(z)$
with the symmetric multiaffine polarization of $\overline Q$ evaluated
at $z-\beta_1,\ldots,z-\beta_q$. All arguments are in the same open
upper or lower half-plane when $\Im z$ lies outside their root strip.
The half-plane polarization supplier therefore gives

$$
C_t(z)=0\ \Longrightarrow\
\min_j\Im\beta_j(t)\le\Im z\le\max_j\Im\beta_j(t),
\qquad
J(t)=0\ \Longrightarrow\
\Im\widehat\chi(t)\in[\min_j\Im\beta_j(t),\max_j\Im\beta_j(t)].
\tag{LC314}
$$

This necessary condition uses the actual kernel, with no real-root
assumption on it at a complex parameter. If $t=a+iy\in\mathcal D$,
the vertical segment is in the same disc and (LC313) gives
$|\Im\widehat\chi(t)|\ge3|y|/4$. Under $\mathsf K$ this contradicts
(LC314) unless $y=0$, including on the closed target boundary.
For real parameters, expanding a simple kernel root along the imaginary
direction in $\mathsf K$ gives $|\beta_j'|\le1/4$, with the endpoint
values obtained by continuity. Consequently $\delta_j\ge1/2$.

It follows under $\mathsf K$ that every actual target node is real and
simple, with the original signed product

$$
P_r'S_r=\left(\frac{\widehat H}{H}\right)^2
 [\partial_zC_t(\lambda_i)]^2
 \left(\sum_j\omega_{ij}\delta_j\right)
 \left(\sum_j\omega_{ij}\gamma_j\right)>0.
\tag{LC315}
$$

Both $H$ and $\widehat H$ are the nonzero real amplitudes of the
original interfaces. Their squared ratio is retained without an
assumed size bound. On $I$, the branches
$f_i(t)=\widehat\chi(t)-c-\lambda_i(t)$ have derivative at least $1/2$.
Thus the exact count, with both endpoints included, is

$$
N_J(\mathcal D)=\sum_{i=1}^q
 \mathbf1_{\{f_i(t_-)\le0\le f_i(t_+)\}}\le q.
\tag{LC316}
$$

No existence of all $q$ branch nodes is asserted. For $q=0$,
$J=\widehat H$ gives zero target nodes directly.

If a fixed $C_{\rm ker}$ were to certify $\mathsf K$ for the actual
kernels at $q\le C_0L$, $\nu\ge C_{\rm ker}L$, the transmission stage
would require only
$\nu\ge\max\{C_{\rm ker},65536(S+3C_0)\}L$.
The existence of that $C_{\rm ker}$ remains unproved.
For real parameters and $q\ge1$, the already known identity
$\sum_j\gamma_j=q\widehat\eta>0$ supplies a total residue, not
positivity of every residue. Retaining the simple-real-root and
complex-strip clauses of $\mathsf K$, hence $\delta_j>0$, put
$V_t=\partial_tR_{q,t}+\widehat\chi'\partial_zR_{q,t}$. A certificate
that every real-pole residue of $(U_{q,t}-gV_t)/R_{q,t}$ is nonnegative
for some $g>0$ would give $G/J'\ge g$ by (LC312).
This relative certificate too remains unpaid for growing degree.


## A local Euler response pays sign once branch geometry is available

Retain the same complete source and auxiliary functions of
(LC263), (LC276)--(LC280) and (LC284), with
$E=128(S+3C_0)L$, total selected multiplicity $r\le C_0L$,
$1\le q\le r$ and $\nu\ge\max\{256E,128q\}$. The exact core
recurrences remain
$p_0=1,w_0=0$ and
$p_j=(\widehat\chi-v\partial_t-\alpha_j)p_{j-1}$,
$w_j=(\widehat\chi-v\partial_t-\alpha_j)w_{j-1}
 +\widehat\eta p_{j-1}$.
This conditional analytical application reuses the exact Euler identity;
it does not assume the kernel residue condition in $\mathsf K$.
It instead requires a quantitative local branch certificate, whose
availability for growing degree is likewise unresolved.

Let $t_0$ be a real actual node with $|t_0-c|\le D/64$ and fix
$\delta>0$. Put

$$
h=\frac{\delta}{64(q+E\delta/D)}\le\frac D{64E}.
\tag{LC317}
$$

The additional certificate is that, throughout $[t_0,t_0+h]$,
$p_q=\prod_{k=1}^q f_k$ with real $C^1$ factors satisfying
$1/2\le f_k'\le3/2$, exactly one $f_j(t_0)=0$, and
$|f_k(t_0)|\ge\delta$ for $k\ne j$.
The segment lies within $|t-c|<D/32$. The certificate concerns
factor geometry, not $G$ or its sign, and is not asserted for every
actual node. For $q=1$ the other-factor condition is empty.

### Bound the endpoint independently of its sign

On nested complex discs with radii
$D/16-jD/(32q)$, $j=0,\ldots,q$, the complete jets give
$|\widehat\chi-\alpha_j|<2D$,
$|v|\le4D^2/\nu$, $|\widehat\eta|\le3/2$ and
$|\widehat\ell|+|\widehat s|\le E/D$.
Cauchy's estimate across a radius step $D/(32q)$ makes the recursive
operator norm at most $2D+128qD/\nu\le3D$. Induction yields

$$
\|p_q\|_{D/32}\le(3D)^q,\qquad
\|w_q\|_{D/32}\le\frac{3q}{2}(3D)^{q-1}.
\tag{LC318}
$$

The other $f_k$ retain their signs on the short segment, and their
product has magnitude at least
$\delta^{q-1}(1-3/(128q))^{q-1}\ge(125/128)\delta^{q-1}$.
Moreover $\widehat H(s)/\widehat H(t_0)\ge e^{-Eh/D}>1/2$.
Direct differentiation gives

$$
J'(s)=\widehat H(s)\prod_{k\ne j}f_k(s)
 \left[f_j'(s)+f_j(s)
  \left(\widehat\ell(s)+\sum_{k\ne j}\frac{f_k'(s)}{f_k(s)}\right)\right].
\tag{LC319}
$$

Here $0\le f_j(s)\le3h/2$,
$\sum_{k\ne j}|f_k'/f_k|\le3q/\delta$ and the second bracket term
has magnitude at most $3/32$. The bracket is at least $13/32$.
Thus $J'(s)$ has the sign of $J'(t_0)$ on the whole segment, with

$$
\begin{gathered}
|J'(s)|>d:=\frac18|\widehat H(t_0)|\delta^{q-1},\qquad
|J'(t_0)|\ge\frac12|\widehat H(t_0)|\delta^{q-1},\\
|G(t_0+h)|\le M:=2|\widehat H(t_0)|(3D)^{q-1}(3E+3q/2),\\
M/d\le B:=16(3E+3q/2)(3D/\delta)^{q-1}.
\end{gathered}
\tag{LC320}
$$

The endpoint estimate uses (LC318),
$G=\widehat H(\widehat s p_q+w_q)$ and
$|\widehat H(t_0+h)|<2|\widehat H(t_0)|$.
The common nonzero amplitude cancels in $M/d$; no absolute amplitude
floor or endpoint sign has been assumed.

### Keep and suppress the homogeneous contribution

Apply the original exact identity $J'=G-(t/n)G'$ from (LC280).
Integrating the derivative of $G(s)s^{-n}$ over only the short segment
gives

$$
\begin{gathered}
G(t_0)=\beta G(t_0+h)+nt_0^n
 \int_{t_0}^{t_0+h}J'(s)s^{-n-1}\,ds,\\
\beta=\left(\frac{t_0}{t_0+h}\right)^n
 \le e^{-nh/(2c)},\qquad
nt_0^n\int_{t_0}^{t_0+h}s^{-n-1}\,ds=1-\beta.
\end{gathered}
\tag{LC321}
$$

The actual endpoint term is retained. If
$nh/(2c)>\log[4(1+B)]$, then
$\operatorname{sgn}(J'(t_0))G(t_0)>3d/4$ and the original coupled
node margin is

$$
P_r'(t_0)S_r(t_0)>\frac3{64}
 \left(\frac{\widehat H(t_0)}{H(t_0)}\right)^2\delta^{2q-2}
 >\frac1{32}\left(\frac{\widehat H(t_0)}{H(t_0)}\right)^2
 \delta^{2q-2}>0.
\tag{LC322}
$$

The endpoint bound is essential: adding a homogeneous term proportional
to $t^n$ leaves the Euler identity unchanged and need not preserve sign.

### A fixed linear budget pays every larger degree parameter

Suppose the geometric certificate is available with
$\delta=D/(K\sqrt{\nu q})$ for a fixed $K\ge1$.
Write $E=C_EL$, where $C_E=128(S+3C_0)$, and define fixed constants

$$
\begin{aligned}
a&=KC_0^{3/2},& b&=\max\{1,3K\sqrt{C_0}\},\\
P&=\max\{1,48C_E+24C_0\},&
A&=\log(8P)+1+C_0(1+\log b),\qquad U=a+C_E,\\
C_*&=\max\{1,256C_E,128C_0,(1024AU)^4\}.
\end{aligned}
\tag{LC323}
$$

For every $\nu\ge C_*L$, put $\Lambda=\nu/L\ge C_*$.
The exponent and endpoint bound obey

$$
\begin{gathered}
X:=\frac{nh}{2c}
 =\frac{\nu T}{128\rho(Kq\sqrt{\nu q}+E)}
 \ge\frac{\sqrt\Lambda\,T}{16UL}
 \ge\frac{\sqrt\Lambda\,L^2}{192U},\\
B\le PL(bL\sqrt\Lambda)^{C_0L},\qquad
\log[4(1+B)]\le AL(1+\log L+\log\Lambda)
 \le AL^2(1+\log\Lambda).
\end{gathered}
\tag{LC324}
$$

Indeed $q\sqrt{\nu q}\le C_0^{3/2}L^2\sqrt\Lambda$,
$\rho\le1/8$, $L>3$ and
$T=e^L-2\ge e^L/2\ge L^3/12$. Also
$1+\log\Lambda\le4\Lambda^{1/4}$ for $\Lambda\ge1$.
The choice (LC323) ensures
$\sqrt\Lambda/(192U)\ge(1024/192)A\Lambda^{1/4}
 >4A\Lambda^{1/4}$, so $X>\log[4(1+B)]$.
Both initial thresholds are paid. This holds for every larger $\nu$,
uniformly for $T\ge32$ and all $0<\rho\le1/8$.

This gives a conditional sign route at the stated central real nodes
if growing-core branch geometry and the quantitative gap are supplied.
It does not certify reality, a gap at every node, or target-boundary
crossings. Reapplying it to $q\le3$ is reuse: (LC293)--(LC303) already
give stronger results on that paid range. Likewise (LC218) and (LC245)
remain suppliers at their larger or adaptive budgets.

The complete-kernel certificate $\mathsf K$ and this quantitative
geometric certificate are two different unpaid routes. The exact
dual-kernel reduction, common-weight transmission and Euler endpoint
estimate do not discharge either certificate at growing degree.
No local all-critical premise has been removed, no FIB ATOM bridge to
these complete signed responses has been established, and RH and
strict Robin for every integer $H>5040$ remain unproved.

## Wider analytic room pays the original response at every target node

Retain the complete source and all local critical-zero and full-removal
premises of (LC263), the regrouping (LC284), total selected multiplicity
$r\le C_0L$, and core degree $q\le r$. Every far selected factor and
possibly nonreal infinite exterior zero remains in $\widehat A$.
The dual kernels and coupled responses are those of (LC305)--(LC308).
This analytical application reuses the common-weight and Euler interfaces;
its extra value-kernel geometry is a stated hypothesis, not a conclusion
about the actual source. No Lean or originality certification is supplied.

For $q\ge1$, use $E=C_EL=128(S+3C_0)L$ and
$\nu\ge\max\{512E,256q\}$. Retain the closed target
$\mathcal D=\{|t-c|\le D/16\}$ and its real diameter $I$, and enlarge
only the real certificate interval to
$I^+=[c-D/16,c+D/12]$. For a fixed $K\ge1$, put
$\delta=D/(K\sqrt{\nu q})$.
Assume the following quantitative value-kernel certificate:

* on $I^+$, $R_{q,t}$ has simple ordered real roots $\beta_j(t)$ with
  $|\beta_j'(t)|\le1/4$;
* its mesh is at least $\delta$ throughout $I^+$ when $q\ge2$;
* for every $t\in\mathcal D$ and every root $\beta$ of $R_{q,t}$,
  $|\Im\beta|\le|\Im t|/4$.

For $q=1$, the mesh condition is empty. No individual response residue
$\gamma_j>0$ is assumed. This certificate requires quantitative value
geometry on a wider interval than $\mathsf K$; neither certificate is
asserted to follow from the already known jets.

The paid bound $|\widehat\ell|+|\widehat s|\le E/D$ on $D/8$
and Cauchy radii $D/40$ and $D/24$ give

$$
\begin{aligned}
|\widehat\eta-1|&\le160E/\nu\le5/16
 &&(|t-c|\le D/10),\\
|\widehat\chi'-1|&\le100E/\nu<1/4
 &&(|t-c|\le D/12).
\end{aligned}
\tag{LC325}
$$

On $D/10$, $|\widehat\chi-\alpha_j|<2D$ and
$|\widehat\eta|<3/2$. Nested radii $D/10-jD/(64q)$ end at
$27D/320>D/12$. The exact recurrence norm is now
$2D+256qD/\nu\le3D$, so (LC318) holds on $D/12$.
Mesh preservation and the common speed weights (LC310) give real factors
$f_i=\widehat\chi-c-\lambda_i$ with $1/2<f_i'<3/2$ on $I^+$.
At each actual real $t_0\in I$, one factor vanishes and the others
have magnitude at least $\delta$. In (LC317),
$h\le D/(64E)<D/48=D/12-D/16$, using $E>384$.
Thus $[t_0,t_0+h]\subset I^+$ even at either target endpoint.

Apply (LC319)--(LC322) with this larger endpoint disc. The common
nonzero $\widehat H$ amplitude and its actual homogeneous endpoint
term are retained; $M/d\le B$ is unchanged. Reusing $a,b,P,A,U$
and the uniform budget argument of (LC323)--(LC324), only the initial
thresholds increase:

$$
\begin{gathered}
C_*^+=\max\{1,512C_E,256C_0,(1024AU)^4\},\qquad
\nu\ge C_*^+L,\\
P_r'(t_0)S_r(t_0)>\frac1{32}
 \left(\frac{\widehat H(t_0)}{H(t_0)}\right)^2
 \delta^{2q-2}>0
 \quad\text{at every actual real }t_0\in I.
\end{gathered}
\tag{LC326}
$$

This covers every larger $\nu$, uniformly for $T\ge32$ and
$0<\rho\le1/8$. Both original amplitudes survive the return to $P_r'S_r$.

The assumed complex strip and (LC325) exclude every nonreal target
node by (LC314). The real branches are strictly increasing, so all
actual nodes on the closed target are simple, at most $q$, and have
exactly the inclusive endpoint count (LC316). The case $q=0$ is again
$J=\widehat H\ne0$.
Thus quantitative wider value geometry would suffice for the entire
conditional local target without a separate positive-residue hypothesis
on $U_{q,t}$. This does not assert positivity of every $\gamma_j$ at every
real parameter. The wider geometry, its growth-degree uniformity, and
removal of the local all-critical premise remain unproved. The argument
supplies no actual growing-core certificate, FIB ATOM bridge, RH proof,
or strict Robin conclusion for every integer $H>5040$.

## A restricted growing-core certificate from the complete matrix pair

Retain the original source, the local critical-zero and complete-removal
premises of (LC263), and the full regrouping (LC284). In particular, every
source zero in the closed radius-$4\rho$ disc about $1/2+iT$ is assumed
critical and fully removed; no condition is imposed on exterior zeros.
Form the full selected factor $Q$ with every such multiplicity first,
then write $Q=Q_{\rm core}Q_{\rm far}$ as in (LC284).
Use the complete $\widehat A=F/Q_{\rm core}$, both nonzero amplitudes
$H,\widehat H$, and the exact kernels (LC305)--(LC308). Write
$E=C_EL$, where $C_E=128(S+3C_0)$, and retain $r\le C_0L$, $q\le r$,
$T\ge32$, $0<\rho\le1/8$, $c=T^2$, $D=T\rho$, and
$\nu=n\rho^2/T^2$ for a positive integer $n$.

The following is a repo-derived conditional analytical application, with
no Lean or originality certification. The Appell recurrence, multiplication
matrix, determinant differentiation, Hermite comparison and Riesz
perturbation argument are generic tools, not new general theorems.
For the Appell recurrence, Srivastava, Jabee and Shadab,
[*Differential equation and recurrence relations of the Sheffer-Appell
polynomial sequence: A matrix approach*, arXiv:1903.09620v1](https://arxiv.org/html/1903.09620v1),
Theorem 4, equation (3.23), applies with $h(u)=u$ and
$l(u)=M_t(u)^{-1/2}$ as a normalized local germ. Its generating factor
$[l(h^{-1}(u))l(u)]^{-1}$ is then exactly $M_t(u)$.
Finite nilpotent matrix encodings of Appell families are classical; see
Aceto, Malonek and Tomaz, [*A unified matrix approach to the representation
of Appell polynomials*, arXiv:1406.1444v1](https://arxiv.org/html/1406.1444v1),
section 3, Theorem 1, for the transfer-matrix construction. That theorem
does not supply the complete-source spectral estimates below.
The shared-weight and polarization transmission (LC309)--(LC316) is
reused without another proof.

### Quantitative range

Put $\delta=E/\nu$ and $\varepsilon=D/c=\rho/T\le1/256$.
For $q\ge1$, the sufficient conditions are

$$
\nu\ge2^{24}(E+q),\qquad
\Theta_q:=(\delta+\varepsilon)\frac{q^{3/2}}{\sqrt\nu}
\le2^{-19}.
\tag{LC327}
$$

Under these conditions the actual $R_{q,t}$ has simple real roots for
real $t\in I$, and its roots have compatible holomorphic labels on the
whole closed $\mathcal D=\{|t-c|\le D/16\}$. Every label obeys
$|\beta_j'|<1/4$ and $|\Im\beta_j(t)|\le|\Im t|/4$.
For real $t\in I$, every actual response residue is greater than $3/4$.
These conclusions are derived from the complete jets, rather than added
as a kernel certificate. The local critical-zero premise is retained.

### Preserve the value and response in one finite matrix

Define the local EGF logarithmic coefficients by
$\log M_t(u)=\sum_{m\ge2}\kappa_m(t)u^m/m!$.
They are ordinary logarithmic coefficients; no identification with
finite-free cumulants is used. Direct differentiation of (LC305) gives

$$
\partial_u\log M_t(u)
=\widehat\chi(\psi_t(u))-\widehat\chi(t),\qquad
b_t'(u)=\widehat\eta(\psi_t(u)),\qquad
\kappa_2=-\frac{t^2}{n}\widehat\chi'.
\tag{LC328}
$$

The paid jets imply
$|\widehat\chi'-1|\le68\delta$ and
$|\widehat\eta-1|\le64\delta$ on $\mathcal D$.
Thus there is a holomorphic choice
$\sigma=(t/\sqrt n)\sqrt{\widehat\chi'}$, positive on $I$, with
$D/(2\sqrt\nu)\le|\sigma|\le2D/\sqrt\nu$.

On $\mathbb C^q$ in its standard orthonormal basis, let
$Ye_j=\sqrt j\,e_{j-1}$, $Ye_0=0$. Then $Y^q=0$ and
$\|Y\|\le\sqrt q$. Define

$$
\begin{aligned}
\mathcal A_q
&=\sigma Y^*-
 \sum_{k=1}^{q-1}\frac{\kappa_{k+1}}{k!\sigma^k}Y^k
 =\sigma(Y^*+Y)+\mathcal E_q,\\
\mathcal B_q&=b_t'(Y/\sigma)
 =\widehat\eta\bigl(\psi_t(Y/\sigma)\bigr),\\
R_{q,t}(z)&=\det(zI-\mathcal A_q),\qquad
\frac{U_{q,t}(z)}{R_{q,t}(z)}
 =\operatorname{tr}\bigl[(zI-\mathcal A_q)^{-1}\mathcal B_q\bigr].
\end{aligned}
\tag{LC329}
$$

All analytic matrix functions here mean finite Taylor evaluation at a
nilpotent matrix. To check the first identity, the generating function
$e^{zu}M_t(u)$ gives
$zR_j=R_{j+1}-\sum_{k=1}^j\binom jk\kappa_{k+1}R_{j-k}$.
Multiplication by $z$ modulo $R_q$, in the basis
$R_j/(\sigma^j\sqrt{j!})$, has matrix $\mathcal A_q$.
For the second identity, vary the germ formally as $M_t e^{h b_t}$,
holding $\sigma$ fixed. The polynomial derivative is the actual $U_q$,
and the multiplication matrix becomes $\mathcal A_q-h\mathcal B_q$.
Jacobi's determinant formula gives the stated trace. This tangent
calculation preserves the original response; it does not change the
actual source or choose an Euler homogeneous term.

If $\Pi_j$ is a rank-one Riesz projection at a simple root, then

$$
\gamma_j=\operatorname{tr}(\Pi_j\mathcal B_q),\qquad
|\gamma_j-\widehat\eta|
\le\|\Pi_j\|\,\|\mathcal B_q-\widehat\eta I\|.
\tag{LC330}
$$

The trace norm of a rank-one operator equals its operator norm. No
factor $q$ is lost in this individual-residue estimate.

### Complete jets bound the finite matrices

The product rule and (LC276), with $E$ replacing $C_1L$, give

$$
\begin{aligned}
\frac{|\widehat\chi^{(j)}|}{j!}
 &\le5\delta16^jD^{1-j} &&(j\ge2),\\
\frac{|\widehat\eta^{(j)}|}{j!}
 &\le128\delta(32/D)^j &&(j\ge1).
\end{aligned}
\tag{LC331}
$$

For the first line the three product terms are at most
$\delta D^{1-j}(4\,16^j+4\,16^{j-1}+16^{j-2})$.
For the second they are at most
$\delta(16/D)^j[64(j+1)+4j+(j-1)/16]$,
which is bounded by the displayed right side.
Put $r_0=\sqrt{q/\nu}$ and $a=t/(n\sigma)$, and set

$$
\Delta=\psi_t(Y/\sigma)-tI
=-\frac{\sigma}{\widehat\chi'}Y(I+aY)^{-1},\qquad
r_0\le2^{-12},\quad
\|aY\|\le2\varepsilon r_0,\quad
\|\Delta\|\le2|\sigma|\sqrt q\le4Dr_0.
\tag{LC332}
$$

The exact value remainder and the resulting estimates are

$$
\begin{aligned}
\mathcal E_q
 &=-\sigma aY^2(I+aY)^{-1}
 -\sum_{j\ge2}\frac{\widehat\chi^{(j)}}{j!}\Delta^j,\\
\|\mathcal E_q\|
 &\le2^{15}|\sigma|(\delta+\varepsilon)q/\sqrt\nu,\\
\|\mathcal B_q-\widehat\eta I\|
 &\le2^{15}\delta r_0.
\end{aligned}
\tag{LC333}
$$

The sums terminate by nilpotence. The first value term costs at most
$3|\sigma|q/\sqrt n$. The rest costs at most
$5\delta D\sum_{j\ge2}(16\|\Delta\|/D)^j
\le20480\delta|\sigma|q/\sqrt\nu$.
The response estimate uses
$128\delta\sum_{j\ge1}(32\|\Delta\|/D)^j
\le2^{15}\delta r_0$.
All coefficients of the complete source up to the required order
remain in these finite evaluations.

For parameter differentiation, freeze $\sigma$ at the point being
evaluated. This keeps a fixed basis while the actual source parameter
changes. Differentiating (LC328) yields

$$
\begin{gathered}
\partial_t[\widehat\chi(\psi_t(u))-\widehat\chi(t)]
=\widehat\chi'(\psi_t(u))(1+tu/n)^{-2}-\widehat\chi'(t),\\
\|\dot{\mathcal A}^{\rm fr}_q\|
\le40960\delta r_0+10\varepsilon r_0
\le2^{16}(\delta+\varepsilon)r_0.
\end{gathered}
\tag{LC334}
$$

Indeed (LC331) bounds the first change of $\widehat\chi'$ by
$80\delta\sum_{j\ge1}(j+1)(16\|\Delta\|/D)^j
\le20480\delta r_0$; use
$\|(I+aY)^{-2}\|\le2$ and
$\|(I+aY)^{-2}-I\|\le4\|aY\|$.
No scalar evaluation outside the target is assumed: these are bounds
from the full jets at $t$ and finite nilpotent Taylor calculus.
They apply at closed-boundary parameters as well.

### Isolated spectrum pays every individual response

The real symmetric Jacobi matrix $Y+Y^*$ has the simple roots $h_j$
of probabilist Hermite $\mathrm{He}_q$ as eigenvalues. The standard
Hermite equation for $w=e^{-x^2/4}\mathrm{He}_q(x)$ is
$w''+(q+1/2-x^2/4)w=0$.
Integration between adjacent zeros and the Dirichlet Poincare inequality
give

$$
h_{j+1}-h_j\ge\frac\pi{\sqrt{q+1/2}}>\frac2{\sqrt q}.
\tag{LC335}
$$

For complex $t$, the matrix $\sigma(Y+Y^*)$ is still normal.
By (LC327) and (LC333),
$\|\mathcal E_q\|\le|\sigma|/(16\sqrt q)$.
The circles of radius $|\sigma|/(4\sqrt q)$ about $\sigma h_j$
are disjoint. On each circle the normal reference resolvent is bounded
by the reciprocal radius; the perturbation ratio is at most $1/4$.
The Neumann series, homotopy count and Riesz integral therefore give
one simple eigenvalue in each circle and

$$
\|\Pi_j\|\le4/3,
\qquad \operatorname{mesh}(R_{q,t})\ge\sigma/\sqrt q
\quad(t\in I,\ q\ge2).
\tag{LC336}
$$

The disjoint labels are holomorphic throughout $\mathcal D$ and a
neighborhood of its boundary. At real parameters each circle is
conjugation-invariant, so its unique root is real.
Using (LC330), (LC333) and the first condition of (LC327) gives

$$
|\gamma_j-\widehat\eta|\le2^{16}\delta r_0\le2^{-20},
\qquad |\widehat\eta-1|\le2^{-18},
\qquad \gamma_j>3/4\quad(t\in I).
\tag{LC337}
$$

For $q\ge2$, the frozen-basis eigenvalue derivative satisfies

$$
|\beta_j'|
=|\operatorname{tr}(\Pi_j\dot{\mathcal A}^{\rm fr}_q)|
\le2^{17}(\delta+\varepsilon)r_0
\le\frac1{4q}\le\frac18<\frac14.
\tag{LC338}
$$

For $q=1$, $R_{1,t}=z$, $U_{1,t}=\widehat\eta$, so
$\beta_1'=0$ and the same residue conclusion holds directly.
Integrating each label along the vertical segment from $\Re t$ to $t$
inside the closed disc gives
$|\Im\beta_j(t)|\le|\Im t|/4$.
This proves every clause of $\mathsf K$ in the restricted range (LC327).

There is also a relative signed certificate. Let
$V_{q,t}=\partial_tR_{q,t}+\widehat\chi'\partial_zR_{q,t}$ and
$\delta_j=\widehat\chi'-\beta_j'$. For real $t$,
$1/2<\delta_j<3/2$, so both $U_q/R_q$ and
$(U_q-V_q/2)/R_q$ have real simple poles and strictly positive residues.
They are strictly proper rational functions and have strictly negative
imaginary part on the upper half-plane. This is a statement about
the actual finite pair at fixed real $t$, not a Pick-closure assertion
for the infinite exterior or an iterative reciprocal gauge.

### A fixed linear budget covers an unbounded restricted degree range

Let

$$
A_*=1+C_E+C_0,\qquad C_{\rm part}=2^{30}A_*^3.
\tag{LC339}
$$

If $1\le q\le C_0L^{1/3}$ and $\nu\ge C_{\rm part}L$, then
$E+q\le(C_E+C_0)L$ pays the first condition of (LC327), and

$$
\Theta_q\le C_0^{3/2}
\left(\frac{C_E}{C_{\rm part}^{3/2}}
+\frac1{256\sqrt{C_{\rm part}}}\right)
\le2^{-45}+2^{-23}<2^{-19}.
\tag{LC340}
$$

Both inequalities improve with every larger $\nu$. The constants are
fixed in $T,\rho,n$, depending only on the supplied source constants
and $C_0$. The original total selected multiplicity may still grow
to $C_0L$; all its far factors remain in $\widehat A$.

Apply (LC310)--(LC316) to these now-certified actual kernels. At every
actual target node, the same nonnegative row weights, with
$\sum_j\omega_{ij}=1$, give the exact original amplitudes

$$
P_r'=\frac{\widehat H}{H}\partial_zC_t(\lambda_i)
 \sum_j\omega_{ij}\delta_j,\qquad
S_r=\frac{\widehat H}{H}\partial_zC_t(\lambda_i)
 \sum_j\omega_{ij}\gamma_j.
$$

For the ratio, use
$\widetilde\omega_{ij}=\omega_{ij}\delta_j/
\sum_k\omega_{ik}\delta_k$ from (LC312).
Since $\delta_j>1/2$, $\delta_j<3/2$ and $\gamma_j>3/4$,
the complete original quantities satisfy

$$
\frac{G}{J'}>\frac12,\qquad
P_r'S_r>\frac38
 \left(\frac{\widehat H}{H}\right)^2
 [\partial_z C_t(\lambda_i)]^2>0,
\qquad
N_J(\mathcal D)=\sum_{i=1}^q
 \mathbf1_{\{f_i(t_-)\le0\le f_i(t_+)\}}\le q.
\tag{LC341}
$$

Every target node is real and simple, including either endpoint;
no existence of all $q$ nodes is asserted. Both original amplitudes
are retained without a size assumption. For $q=0$, the unchanged
identity $J=\widehat H\ne0$ gives no target nodes.
The fixed source constants have not been numerically instantiated.

This restricted unbounded-degree application uses the already-paid
fixed-degree results without recertifying $q\le3$. It does not meet
the full $q\le C_0L$ target: at $q\asymp C_0L$ and $\nu=C_*L$,
the source part of $\Theta_q$ has order
$C_EC_0^{3/2}L/C_*^{3/2}$. No fixed $C_*$ makes this absolute-norm
perturbation condition small for every $L$. The loss comes from
comparison with the microscopic Hermite gap, not a counterexample
to the actual kernels. At full growth the missing step is simple real
spectrum with sufficiently bounded individual projections for the
complete matrix. The local all-critical premise, that full-growth
estimate, a FIB ATOM bridge, RH and strict Robin for every integer
$H>5040$ remain unresolved.

## Matching two complete logarithmic coefficients enlarges the real range

Retain the complete source, local all-critical selection and removal,
all multiplicities, $Q=Q_{\rm core}Q_{\rm far}$, and
$\widehat A=F/Q_{\rm core}=AQ_{\rm far}$ from (LC263), (LC284)
and (LC304). All distant selected factors and every possibly nonreal
infinite exterior zero remain in $\widehat A$. Keep the nonzero original
amplitudes $H,\widehat H$, $r\le C_0L$, $q\le r$, $T\ge32$,
$0<\rho\le1/8$, $L=\log(T+2)$, $c=T^2$, $D=T\rho$,
$\nu=n\rho^2/T^2$, and $E=C_EL$, $C_E=128(S+3C_0)$.

This is a conditional analytical application, without Lean or originality
certification. The complete Appell representation (LC328)--(LC330),
classical Laguerre finite series, recurrences and differential equation,
Riesz perturbation argument and common-weight source transmission are
reused. The finite Laguerre series is already cited in (LC1) and (LC199),
the derivative in (LC6), and the recurrence and spacing proof in
(LC210). The Gaussian/Hermite limit is also reused. These suppliers are
[DLMF 18.5.12](https://dlmf.nist.gov/18.5.E12),
[18.9.13--14](https://dlmf.nist.gov/18.9#E13),
[18.9.23](https://dlmf.nist.gov/18.9.E23), and
[Table 18.8.1](https://dlmf.nist.gov/18.8#T1).
The additional estimate transports the actual complete value and response
into one Laguerre frame; it does not substitute the reference source for
$\widehat A$.

### Match the actual quadratic and cubic logarithmic coefficients

Suppress hats only on $\chi,\eta$ in this section. At a parameter
$t\in\mathcal D=\{|t-c|\le D/16\}$ put

$$
\sigma^2=v\chi',\quad v=t^2/n,\quad \tau=t/n,\quad
\delta=E/\nu,\quad\varepsilon=D/c,\quad
h=\frac{\kappa_3}{2\sigma^2}
 =\tau+\frac{v\chi''}{2\chi'},\quad
\mu=h/\sigma,\quad\vartheta=h-\tau.
\tag{LC342}
$$

Use the previous holomorphic choice of $\sigma$, positive on the real
interval $I=[c-D/16,c+D/16]$. For $h\ne0$ set $N=\mu^{-2}$ and
$M_L(u)=e^{-Nhu}(1+hu)^N$ as a germ at zero. Its logarithmic derivative
and first two nonzero logarithmic coefficients are

$$
f_L(u)=-\frac{\sigma^2u}{1+hu},\qquad
\kappa_2^L=-\sigma^2,\qquad\kappa_3^L=2h\sigma^2.
\tag{LC343}
$$

They match the actual $M_t$ exactly. At $h=0$ use
$M_L=e^{-\sigma^2u^2/2}$; every finite formula below has this regular
Gaussian limit. No integer condition on $N$ is imposed.

### Transport the reference connection into the actual Appell frame

For $h\ne0$, define
$\mathscr P_j(z)=j!h^jL_j^{(N-q)}(N-z/h)$.
The classical recurrence gives

$$
z\mathscr P_j=\mathscr P_{j+1}+h(q-1-2j)\mathscr P_j
 +j[\sigma^2-(q-j)h^2]\mathscr P_{j-1}.
\tag{LC344}
$$

This recurrence also defines the polynomials at $h=0$. Its degree-$q$
member is the reference Appell polynomial $R_q^L$ generated by
$e^{zu}M_L(u)$. The lower $\mathscr P_j$ use the fixed parameter $N-q$;
they are not the lower reference Appell polynomials $R_j^L$.
Set

$$
a_j=1-(q-j)\mu^2,\qquad
n_j=\sigma^j\sqrt{j!\prod_{k=1}^j a_k},\qquad
\frac{\mathscr P_j}{n_j}
 =\sum_{k=0}^{q-1}\mathsf T_{kj}
       \frac{R_k^L}{\sigma^k\sqrt{k!}}\quad(0\le j<q).
\tag{LC345}
$$

The square roots take their positive values at real parameters.
When $q|\mu|^2\le1/16$, they have holomorphic choices. The triangular
connection $\mathsf T$ is invertible, with diagonal
$\prod_{k=1}^j a_k^{-1/2}$.
Apply this same connection to the **actual** Appell sequence:

$$
\mathscr Q_j
 =\sum_{k=0}^{q-1}\mathsf T_{kj}
     \frac{R_{k,t}}{\sigma^k\sqrt{k!}}
 =\left(\frac{M_t}{M_L}\right)(\partial_z)
      \frac{\mathscr P_j}{n_j}.
\tag{LC346}
$$

Thus the actual basis is $\mathscr Q_j$, rather than the literal
reference polynomials $\mathscr P_j/n_j$. All germ evaluations on
polynomials or nilpotent matrices are finite Taylor evaluations.
With $D_0=Y/\sigma$ and $f_t(u)=\chi(\psi_t(u))-\chi(t)$, the supplied
Appell formula gives $\mathcal A_M-\mathcal A_L=-(f_t-f_L)(D_0)$.
The same similarity consequently preserves the complete pair:

$$
\begin{aligned}
\mathsf D&=\mathsf T^{-1}D_0\mathsf T
 =\sigma^{-1}W(I-\mu W)^{-1},
 &We_j&=\frac{\sqrt j}{\sqrt{a_j}}e_{j-1},\\
\widetilde A&=\mathsf T^{-1}\mathcal A_M\mathsf T
 =J-(f_t-f_L)(\mathsf D),
 &J_{jj}&=h(q-1-2j),\\
\widetilde B&=\mathsf T^{-1}\mathcal B_M\mathsf T
 =\eta\bigl(\psi_t(\mathsf D)\bigr),
 &J_{j,j+1}&=J_{j+1,j}=\sigma\sqrt{(j+1)a_{j+1}},\\
R_{q,t}(z)&=\det(zI-\widetilde A),
 &\frac{U_{q,t}(z)}{R_{q,t}(z)}
 &=\operatorname{tr}[(zI-\widetilde A)^{-1}\widetilde B].
\end{aligned}
\tag{LC347}
$$

Here $0\le j<q$ for the diagonal and $0\le j<q-1$ for the
superdiagonal. The derivative formula follows from
$\mathscr P_j'=\sum_{k<j}(j!/k!)h^{j-1-k}\mathscr P_k$ and (LC345).
At $h=0$, $\mathsf T=I$ and $\mathsf D=Y/\sigma$.
For real negative $h$, the Laguerre roots are reflected; the symmetric
matrix still has positive off-diagonals. This simultaneous transport
avoids introducing $\|\mathsf T\|\|\mathsf T^{-1}\|$ into the response
bound. It asserts bounds in the transported coordinates.

### The matched complete remainder has no independent binomial cost

Assume $q\ge4$ and

$$
\nu\ge2^{32}(E+q),\qquad 2^{40}\frac{Eq^2}{\nu^2}\le1.
\tag{LC348}
$$

Put $r_0=\sqrt{q/\nu}$. The first condition gives
$\delta\le2^{-32}$, $r_0\le2^{-16}$ and
$\delta+\varepsilon<2^{-7}$.
The complete jets (LC331) and (LC342) give
$|\vartheta|/|\sigma|\le8800\delta/\sqrt\nu$ and
$|\tau|/|\sigma|\le\sqrt2\varepsilon/\sqrt\nu$. Therefore

$$
|\mu|\le2^{14}(\delta+\varepsilon)/\sqrt\nu,\quad
q|\mu|^2<2^{-18},\quad
\|\sigma\mathsf D\|<2\sqrt q,\quad
\|\Delta\|<12Dr_0,
\quad \Delta=-v\mathsf D(I+\tau\mathsf D)^{-1}.
\tag{LC349}
$$

Indeed $\|W\|\le4\sqrt{q/15}$ and
$\|\mu W\|\le1/\sqrt{15}$ give
$\|\sigma\mathsf D\|\le4\sqrt q/(\sqrt{15}-1)<2\sqrt q$.
Also $\|\tau\mathsf D\|\le3\varepsilon r_0<1/4$,
$\|h\mathsf D\|\le1/2$ and
$\|\Delta\|\le(32/3)Dr_0$.
These statements also hold at complex parameters.
Taylor expansion of the actual complete $\chi$ gives the exact
cancellation

$$
(f_t-f_L)(\mathsf D)
 =\sigma^2\vartheta^2\mathsf D^3
   (I+\tau\mathsf D)^{-2}(I+h\mathsf D)^{-1}
 +\sum_{j\ge3}\frac{\chi^{(j)}}{j!}\Delta^j.
\tag{LC350}
$$

The commuting denominators verify it directly. Its first term is at
most $32\cdot8800^2|\sigma|\delta^2q^{3/2}/\nu$, which is less than
$|\sigma|Eq^{3/2}/\nu^2$ because
$32\cdot8800^2\,2^{-32}<1$. For the remaining complete tail,
$192r_0<1/2$ and (LC331) give

$$
\left\|\sum_{j\ge3}\frac{\chi^{(j)}}{j!}\Delta^j\right\|
 \le5\delta D\frac{(192r_0)^3}{1-192r_0}
 \le20\cdot192^3|\sigma|\frac{Eq^{3/2}}{\nu^2}.
$$

No actual coefficient has been discarded. In particular,

$$
\|\widetilde A-J\|
 \le2^{36}|\sigma|\frac{Eq^{3/2}}{\nu^2},\qquad
\|\widetilde B-\eta I\|
 \le2^{18}\delta r_0.
\tag{LC351}
$$

The response bound is
$128\delta(384r_0)/(1-384r_0)\le98304\delta r_0$.
Both estimates hold on the closed complex parameter disc.
The value estimate has no separate $\varepsilon$ term: its pure
binomial contribution is part of the exact reference, and the mixed
terms cancel in (LC350).

### Freeze the complete coordinate change for eigenvalue speed

At an evaluation point $t_0$, freeze both the normalization $\sigma_0$
and the connection $\mathsf T_0$. Differentiating
$\mathsf T_0^{-1}\mathcal A_M(t;\sigma_0)\mathsf T_0$
uses a constant $\mathsf D$ and gives

$$
\dot{\widetilde A}^{\rm fr}=-\partial_t f_t(\mathsf D),\qquad
\partial_t f_t(\mathsf D)
 =\chi'(tI+\Delta)(I+\tau\mathsf D)^{-2}-\chi'(t)I,
\qquad
\|\dot{\widetilde A}^{\rm fr}\|
 <2^{20}(\delta+\varepsilon)r_0.
\tag{LC352}
$$

For $x=16\|\Delta\|/D\le192r_0<1/4$, (LC331) bounds the first
change by $80\delta\sum_{j\ge1}(j+1)x^j\le61440\delta r_0$.
The inverse square has norm at most $2$, and its change from the
identity costs at most $4\|\tau\mathsf D\|$. The combined cost is
$122880\delta r_0+18\varepsilon r_0$.
Freezing these normalizations does not freeze the underlying actual
Appell family. Letting the complete coordinate change vary would add
a commutator $[\widetilde A,K]$. For a simple-root projection $\Pi_j$,
$\operatorname{tr}(\Pi_j[\widetilde A,K])=0$. Thus (LC352) gives the
exact eigenvalue speed, while its norm bound is not a bound on the
full moving-coordinate derivative.

### Real Laguerre spacing pays every individual response

For real $t$ and $h\ne0$, $J$ is self-adjoint and $N\ge16q$.
The removal of the first derivative from the classical Laguerre equation
with parameter $N-q$ gives

$$
w''+V(x)w=0,\qquad
V=-\frac14+\frac{N+q+1}{2x}
 -\frac{(N-q)^2-1}{4x^2},\qquad
V_{\max}=\frac{Nq+(N+q+1)/2}{(N-q)^2-1}\le\frac{2q}{N}.
\tag{LC353}
$$

The existing Dirichlet spacing argument therefore gives
$\Delta x\ge\pi/\sqrt{V_{\max}}$. In the reflected or unreversed
coordinate $z=h(N-x)$,
$\operatorname{gap}(J)\ge\pi\sigma/\sqrt{2q}>2\sigma/\sqrt q$.
Continuity of the real symmetric matrix gives the same bound at $h=0$.
Condition (LC348) and (LC351) put the actual perturbation below
$\sigma/(16\sqrt q)$. The reused Riesz argument on circles of radius
$\sigma/(4\sqrt q)$ gives one simple real root per circle and, in the
transported coordinates,

$$
\|\Pi_j\|\le4/3,\quad
|\gamma_j-\eta|\le\frac43\,2^{18}\delta r_0
 \le\frac43\,2^{-30},\quad
|\eta-1|\le2^{-26},\quad
\gamma_j>3/4,\quad
|\beta_j'|\le\frac43\,2^{20}(\delta+\varepsilon)r_0<1/6<1/4.
\tag{LC354}
$$

These are conclusions for real parameters, including both endpoints.
Simplicity supplies local analytic labels around each real parameter;
it does not supply labels on the entire complex disc.

### A fixed linear budget covers the square-root real degree range

Let $A_*=1+C_E+C_0$ and $C_{\rm real}=2^{48}A_*^3$. Then

$$
4\le q\le C_0\sqrt L,\qquad\nu\ge C_{\rm real}L
\tag{LC355}
$$

implies (LC348): $E+q\le(C_E+C_0)L$ and
$2^{40}Eq^2/\nu^2\le2^{-56}C_EC_0^2/A_*^6<1$.
Both improve for every larger $\nu$, uniformly in all allowed $T,\rho$.
The existing small-degree conclusions are reused.

Use the already-paid real common-weight transmission (LC310)--(LC312).
For every actual real node, put $d_j=\chi'-\beta_j'$, so
$1/2<d_j<3/2$. The same nonnegative weights of sum one give
$P_r'=(\widehat H/H)\partial_zC_t(\lambda_i)\sum_j\omega_{ij}d_j$
and $S_r=(\widehat H/H)\partial_zC_t(\lambda_i)\sum_j\omega_{ij}\gamma_j$.
Consequently, the product and ratio inequalities hold at every actual
real node in the closed interval, and the interval count is

$$
P_r'S_r>\frac38\left(\frac{\widehat H}{H}\right)^2
 [\partial_zC_t(\lambda_i)]^2>0,\qquad
\frac{G}{J'}>\frac12,\qquad
N_J(I)=\sum_{i=1}^q
 \mathbf1_{\{f_i(t_-)\le0\le f_i(t_+)\}}\le q.
\tag{LC356}
$$

Here $f_i=\chi-c-\lambda_i$ and
$f_i'=\sum_j\omega_{ij}d_j>1/2$. This count includes the two real
endpoints and does not assert existence of all $q$ nodes. Both original
amplitudes remain, without any amplitude-size premise.

The analytical increment is the real-parameter range (LC355), rather
than a new general Laguerre theorem. At $q=C_0L$, $\nu=CL$, the
sufficient perturbation budget still contains
$Eq^2/\nu^2=C_EC_0^2L/C^2$; this argument does not pay full growth.
For complex parameters $J$ is complex symmetric and need not be normal.
The complex norm bounds above do not provide uniformly bounded
projections, whole-disc root labels, a strip bound or exclusion of
nonreal actual nodes. In particular, $N_J(I)$ is not a zero count in
$\mathcal D$. The local all-critical premise, actual source constants,
full-growth certificate and the bridge to an unconditional global
statement remain unpaid. RH and strict Robin for every integer
$H>5040$ remain unresolved.

## A complete derivative chain pays the full growing core

Retain the original source, local all-critical selection and complete
removal, all multiplicities, $Q=Q_{\rm core}Q_{\rm far}$, and
$\widehat A=F/Q_{\rm core}=AQ_{\rm far}$ from (LC263), (LC284)
and (LC304). Every far selected factor and every possibly nonreal
infinite exterior zero remains in $\widehat A$. Keep both original
nonzero amplitudes $H,\widehat H$, $T\ge32$, $0<\rho\le1/8$,
$L=\log(T+2)$, $c=T^2$, $D=T\rho$, $r\le C_0L$, $q\le r$,
$\nu=n\rho^2/T^2$, $E=C_EL$ and $C_E=128(S+3C_0)$.
Use exactly the actual kernels and responses in (LC305)--(LC308),
and the holomorphic $\sigma^2=v\chi'$ from (LC342).
Suppress hats only on $\chi,\eta$ in this section.

This is a conditional repository-derived analytical application,
without Lean or originality certification. The complete Appell matrix
and differential equation, Hermite real-root starting point,
holomorphic root continuation, coefficient majorants and finite-free
transmission are reused. The derivative-chain estimate below is
applied to the complete source, including both distinct actual
tangents. It does not estimate the condition numbers of the complex
Laguerre Jacobi matrix.

### Bound the actual finite derivative chain at its own root

For a germ $\Phi(u)=\sum_m\phi_mu^m$, let
$\|\Phi\|_a^\#=\sum_m|\phi_m|a^m$.
At a fixed parameter put $P(z)=M(\partial_z)z^q$,
$M(0)=1$, $M'(0)=0$, and

$$
f(u)=M'(u)/M(u)=-\sigma^2u+g(u),\quad g(u)=O(u^2),\quad
a=8\sqrt q/|\sigma|,\quad
e=\frac{\|g\|_a^\#}{|\sigma|^2a}\le\frac1{16}.
\tag{LC357}
$$

The Appell differential equation is
$(z+f(\partial_z))P'=qP$.
For a published form, Srivastava, Jabee and Shadab,
[*Differential equation and recurrence relations of the Sheffer-Appell
polynomial sequence: A matrix approach*, arXiv:1903.09620v1](https://arxiv.org/html/1903.09620v1),
Theorem 1, equation (2.11), give this specialization with
their $h(u)=u$ and $l(u)=M(u)^{-1/2}$; their Theorem 4,
equation (3.23), gives the corresponding recurrence.
The same equation follows from the existing coefficient recurrence
before (LC330). These general identities are reused.

First use the complete matrix (LC329) only for coarse root location:
$A=\sigma(Y+Y^*)-g(Y/\sigma)$, with
$\|Y/\sigma\|\le a/8$. Since $g$ starts at degree two,
$\|g(Y/\sigma)\|\le\|g\|_a^\#/64$. Every root $\beta$ has

$$
|\beta|\le\|A\|\le(2+e/8)|\sigma|\sqrt q
 <3|\sigma|\sqrt q.
\tag{LC358}
$$

Write the reused differential equation as
$\sigma^2P''-zP'+qP=g(\partial_z)P'$.
Its $k$th derivative at an actual root is

$$
\sigma^2P^{(k+2)}(\beta)
=\beta P^{(k+1)}(\beta)-(q-k)P^{(k)}(\beta)
 +\sum_{m\ge2}g_mP^{(k+m+1)}(\beta).
\tag{LC359}
$$

Set $d_k=P^{(k)}(\beta)/a^k$ for $0\le k\le q$,
and $D_* =\max_k|d_k|$. Monicity gives $d_q\ne0$ and
$D_*>0$, while $d_0=0$. For $0\le k\le q-2$, derivatives of
order greater than $q$ vanish, and (LC358)--(LC359) give

$$
|d_{k+2}|
\le\left(\frac38+\frac1{64}+e\right)D_*
\le\frac{29}{64}D_*<D_*.
\tag{LC360}
$$

Thus the maximum occurs only at $k=1$, also when $q=1$.
In particular every actual root is simple, and

$$
\left|\frac{P^{(m)}(\beta)}{P'(\beta)}\right|
\le a^{m-1}\quad(1\le m\le q),\qquad
\left|\frac{\Phi(\partial_z)P(\beta)}{P'(\beta)}\right|
\le\sum_{m=1}^q|\phi_m|a^{m-1}.
\tag{LC361}
$$

The constant coefficient vanishes at the root. Taylor expansion gives,
for $0<|w|\le1/a$,
$|P(\beta+w)/(P'(\beta)w)-1|\le\exp(1)-2<1$.
No other root is in that closed disc, so distinct roots are more
than $1/a$ apart. Neither this chain nor its coarse location uses
bounded individual spectral projections.

### The complete source pays the chain at a linear budget

Now use the actual $P=R_{q,t}$ and
$g_t=f_t+\sigma^2u$ for every $t\in\mathcal D$.
Assume only the sufficient budget

$$
\nu\ge2^{32}(E+q),\qquad
\delta=E/\nu\le2^{-32},\quad
r_0=\sqrt{q/\nu}\le2^{-16},\quad
\varepsilon=D/c\le2^{-8}.
\tag{LC362}
$$

The inherited complete complex jets (LC313), (LC331) and (LC342)
give $|\chi'-1|\le68\delta$, $|\eta-1|\le64\delta$,
$D/(2\sqrt\nu)\le|\sigma|\le2D/\sqrt\nu$,
$|\tau|/|\sigma|\le2\varepsilon/\sqrt\nu$ and
$|v|\le2|\sigma|^2$, with $\tau=t/n$.
Define the actual scalar displacement
$\Delta(u)=-vu/(1+\tau u)$ and put

$$
A_0=|\tau|a\le16\varepsilon r_0\le2^{-20},\quad
d=\|\Delta\|_a^\#=\frac{|v|a}{1-A_0}
 \le32|\sigma|\sqrt q\le64Dr_0,\quad
x=16d/D\le1024r_0\le1/64.
\tag{LC363}
$$

These displacement bounds keep the scalar germ within the supplied
analytic room at every parameter; the target disc is not reduced.
The actual $f_t(u)=\chi(t+\Delta(u))-\chi(t)$ gives exactly

$$
g_t(u)=\frac{\sigma^2\tau u^2}{1+\tau u}
 +\sum_{j\ge2}\frac{\chi^{(j)}(t)}{j!}\Delta(u)^j.
\tag{LC364}
$$

The full logarithmic remainder is retained. Coefficient majorants and
(LC331) give

$$
\|g_t\|_a^\#
\le|\sigma|^2a\frac{A_0}{1-A_0}
 +5\delta D\frac{x^2}{1-x},\qquad
e_t\le(2^{22}\delta+32\varepsilon)r_0
\le2^{-26}+2^{-19}<2^{-18}<1/16.
\tag{LC365}
$$

Here $|\sigma|^2a=8|\sigma|\sqrt q\ge4Dr_0$.
The geometric sums in (LC364)--(LC365) include every higher
coefficient of the complete source; no Schwarzian sign or independent
high-order cancellation is assumed. The finite-chain bound (LC361)
therefore holds at every actual root of every complex-parameter
$R_{q,t}$.

### Establish real roots before continuing the actual labels

At a real parameter, the actual coefficients and $\sigma$ are real,
with $\sigma>0$. For $0\le\lambda\le1$, use only as a proof device

$$
M_\lambda(u)=\exp\left(-\sigma^2u^2/2
 +\lambda\int_0^u g_t(w)\,dw\right),\qquad
P_\lambda=M_\lambda(\partial_z)z^q.
\tag{LC366}
$$

Its logarithmic remainder is $\lambda g_t$, so (LC357)--(LC361)
exclude multiple roots throughout this real-coefficient homotopy.
At $\lambda=0$ the roots are those of the scaled Hermite polynomial,
all simple and real. A pair of roots could leave the real axis only
through a collision. Thus the actual endpoint $R_{q,t}=P_1$ also has
$q$ simple real roots. This argument does not replace its source or
actual response by the Gaussian model.

The actual coefficients are holomorphic on a neighborhood of
$\mathcal D$, and the actual discriminant is nonzero on the whole
compact disc by (LC365). It remains nonzero on a slightly larger
disc. The existing simple-root continuation argument from (LC336)
supplies compatible holomorphic labels $\beta_j$ there, real on $I$.

### Keep the two distinct actual tangents

At fixed original $z,u$, set $a_t(u)=\partial_t\log M_t(u)$.
Since $M_t(0)=1$ and its linear logarithmic coefficient is identically
zero, $a_t(0)=a_t'(0)=0$. Exact generating functions give

$$
\partial_tR_{q,t}=a_t(\partial_z)R_{q,t},\qquad
U_{q,t}=b_t(\partial_z)R_{q,t},\qquad
a_t'=\partial_tf_t,\quad b_t'=\eta(\psi_t(u)).
\tag{LC367}
$$

The parameter tangent and original response remain different
operations. The complete kernel and its normalizations are
differentiated as actual functions, not frozen as an artificial
family. Using the same $A_0,d,x$ and full jets,

$$
\begin{aligned}
\partial_tf_t(u)
 &=\chi'(t+\Delta(u))(1+\tau u)^{-2}-\chi'(t),\\
\|\chi'(t+\Delta)-\chi'(t)\|_a^\#
 &\le80\delta[(1-x)^{-2}-1]\le320\delta x,\\
\|\partial_tf_t\|_a^\#
 &\le640\delta x+8A_0
 \le(2^{20}\delta+128\varepsilon)r_0<2^{-16},\\
\|\eta(t+\Delta)-\eta(t)\|_a^\#
 &\le128\delta\frac{2x}{1-2x}
 \le2^{19}\delta r_0\le2^{-29}.
\end{aligned}
\tag{LC368}
$$

The inverse-square majorant is below two; its change costs at most
$4A_0$. Integration of the Taylor coefficients of $a_t'$ and
$b_t'-\eta$ and application of the actual-root bound (LC361) give

$$
|\beta_j'|
=\left|\frac{a_t(\partial_z)R_{q,t}(\beta_j)}
 {\partial_zR_{q,t}(\beta_j)}\right|
\le\|\partial_tf_t\|_a^\#<2^{-16}<1/4,\qquad
|\gamma_j-\eta|\le2^{19}\delta r_0,
\quad\gamma_j=\frac{U_{q,t}(\beta_j)}
 {\partial_zR_{q,t}(\beta_j)}.
\tag{LC369}
$$

These estimates hold at every complex parameter, including the closed
boundary. For real parameters, $|\eta-1|\le2^{-26}$ gives
$\gamma_j>3/4$.
The already-established real values and whole-disc holomorphic labels
now permit integration along the vertical segment from $\Re t$ to $t$:
$|\Im\beta_j(t)|\le|\Im t|/4$.

### Reuse the original-node transmission at full growth

Equations (LC366)--(LC369) pay precisely the actual kernel certificate
$\mathsf K$ before (LC314). Apply the existing half-plane polarization
and common nonnegative weights of (LC309)--(LC316).
Every original target node in the entire closed $\mathcal D$ is real
and simple. With $d_j=\chi'-\beta_j'$, both distinct responses use
the same weights and satisfy $1/2<d_j<3/2$, $\gamma_j>3/4$.
Thus both original amplitudes remain in

$$
P_r'S_r>\frac38\left(\frac{\widehat H}{H}\right)^2
 [\partial_zC_t(\lambda_i)]^2>0,\qquad
\frac{G}{J'}>\frac12,\qquad
N_J(\mathcal D)=\sum_{i=1}^q
\mathbf1_{\{f_i(t_-)\le0\le f_i(t_+)\}}\le q.
\tag{LC370}
$$

Here $f_i=\chi-c-\lambda_i$ and $f_i'>1/2$.
Both endpoints are included, and existence of all $q$ original nodes
is not asserted. No amplitude-size premise is added. For $q=0$,
reuse $J=\widehat H\ne0$ directly.

Take $C_{\rm ker}=2^{32}(1+C_E+C_0)$. Then

$$
q\le C_0L,\qquad\nu\ge C_{\rm ker}L
\quad\Longrightarrow\quad\nu\ge2^{32}(E+q).
\tag{LC371}
$$

All sufficient estimates improve for every larger $\nu$, uniformly
in every allowed $T,\rho$. The formerly unpaid full-growth kernel
condition is supplied under the inherited local source premises.
The paid quantity is
$(2^{22}E/\nu+32\varepsilon)\sqrt{q/\nu}$, which is bounded
independently of $L$ at a fixed linear budget. This scalar route has
not established a bound on complex Jacobi spectral projections.

The local all-critical premise, complete removal of those zeros,
source constant instantiation and unconditional global transmission
remain required. The infinite exterior has not been assumed real.
No unconditional local realness, FIB ATOM arithmetic bridge, RH or
strict Robin for every integer $H>5040$ follows without the remaining
premises and global argument.

## Complete local removal does not require critical-line zeros

Keep the unchanged $F(z)=\Xi(\sqrt z)/\xi(1/2)$, $T\ge32$,
$0<\rho\le1/8$, $L=\log(T+2)$, $c=T^2$ and $D=T\rho$.
Keep $n\in\mathbb N_{>0}$ and $\nu=n\rho^2/T^2$.
In this section remove the local all-critical premise. Select instead
**every** zero $\omega$ of $\xi$ in the closed disc
$|\omega-(1/2+iT)|\le4\rho$, with its multiplicity, and set

$$
\Phi(s)=-(s-1/2)^2,\qquad
Q(z)=\prod_{\omega\ \mathrm{selected}}(z-\Phi(\omega)),\qquad
A=F/Q.
\tag{LC372}
$$

The source's functional equation and conjugation make the selection
invariant under $\omega\mapsto1-\overline\omega$.
Since $\Phi(1-\overline\omega)=\overline{\Phi(\omega)}$,
$Q$ has real coefficients, although its roots need not be real.
Every multiplicity and every closed-boundary zero is retained.
The local square map is injective and noncritical at this height,
so the multiplicities removed from $F$ are exactly those selected.
The unit-window count already used in (LC180), (LC193) gives
$r=\deg Q\le C_0L$ after fixing one sufficiently large source constant
$C_0$. No selected-root spacing or realness is used.

This is a repository-derived source-interface extension of the
existing pole-removal and full derivative-chain estimates, without
Lean or originality certification. The fixed Titchmarsh pole sum,
source count, genus-zero product, complete coefficient-circle extraction
and exponential tilt are reused. The added correspondence checks which
inputs survive complete removal of possibly nonreal local zeros.
It supplies no signed convolution estimate for a nonreal core.

### Cancel the actual poles before taking an absolute bound

For each selected $\omega$, the exact factorization is

$$
\Phi(s)-\Phi(\omega)=-(s-\omega)(s-(1-\omega)),\qquad
\frac{\Phi'(s)}{\Phi(s)-\Phi(\omega)}
=\frac1{s-\omega}+\frac1{s-(1-\omega)}.
\tag{LC373}
$$

Thus in
$g(s)=\xi'(s)/\xi(s)-\sum_{\rm selected}
\Phi'(s)/(\Phi(s)-\Phi(\omega))$
all actual near poles cancel with their multiplicities.
The second pole has negative ordinate; on the radius-$2\rho$
working disc its distance is at least $2T-6\rho>T$.
Each unremoved pole in the fixed height window is more than $4\rho$
from the center, hence more than $2\rho$ from this working disc.
The already-cited Titchmarsh Theorem 9.6(A), fixed-window replacement
and Gamma factor estimate from (LC204) therefore give

$$
|g(s)|\le C L/\rho\quad(|s-s_0|\le2\rho),\qquad
|g'(s)|\le C L/\rho^2\quad(|s-s_0|\le\rho).
\tag{LC374}
$$

This is an analytic pole-removed function across every selected zero.
The local inverse and chain rule from (LC205) give
$|A'(c)/A(c)|\le C_bL/D$ and the same local logarithmic-jet bounds,
with no reference to the real parts of the selected zeros.
Since $A,Q,F$ are real, $A(c)$ and that drift are real, including
when $c$ was a removed source zero.

For an unremoved source zero write $\zeta=t_\zeta^2$, with
$t_\zeta=\gamma+i\eta_\zeta$, $\gamma>0$ and $|\eta_\zeta|<1/2$.
Completeness of (LC372) implies $|t_\zeta-T|>4\rho$.
The same square-root clearance, unit-window count and all-height
summation in (LC262)--(LC263) consequently give

$$
\sup_{|a-c|\le D/4}
\sum_{\zeta\in Z(A)}|a-\zeta|^{-2}
\le C_{\rm abs}L/D^2.
\tag{LC375}
$$

Every unremoved zero of the infinite source remains in the sum.
The full coefficient-circle estimates (LC267)--(LC276) use only
(LC374)--(LC375), the reality of $A$, and the source drift.
They therefore supply $H=\mathscr T_nA\ne0$ on $|t-c|\le D/8$
and the same complete complex jets for all $\nu\ge32SL$,
$S=C_{\rm abs}+C_b+1$. This nonvanishing is a conclusion of the
complete source estimate, rather than an additional real-zero premise.

### Regroup the core without imposing real-rootedness

Select $Q_{\rm core}$ by $|\alpha-c|\le D$ among the actual roots of
$Q$, counting multiplicities, and put
$Q_{\rm far}=Q/Q_{\rm core}$,
$\widehat A=AQ_{\rm far}=F/Q_{\rm core}$.
Put $q=\deg Q_{\rm core}$,
$\mathcal D=\{|t-c|\le D/16\}$ and $I=[c-D/16,c+D/16]$.
Both factors have real coefficients because the cutoff is conjugation
invariant. For every $|a-c|\le D/4$, each far root is more than
$3D/4$ away. The existing estimate (LC284) consequently holds as
written, with complex far roots also included:

$$
K_{\widehat A}(a)\le(C_{\rm abs}+2C_0)L/D^2,
\qquad
|\widehat A'(c)/\widehat A(c)|\le(C_b+C_0)L/D.
\tag{LC376}
$$

This uses their absolute distances and count, not positive factors.
All original exterior and far selected zeros remain.
The actual $\widehat H,\widehat\ell,\widehat s,\widehat\chi,
\widehat\eta$ and complete kernels of (LC305) inherit their full jets
with $E=128(S+3C_0)L$ and the nonzero amplitude on the same outer disc.
Apply only the kernel steps (LC357)--(LC369): their derivative-chain,
real-coefficient homotopy and both actual tangents do not require that
$Q_{\rm core}$ itself have real roots. For
$\nu\ge2^{32}(E+q)$ the actual auxiliary kernel therefore has simple
holomorphic labels throughout the closed parameter disc, is real-rooted
on its real diameter, and obeys

$$
|\beta_j'|<2^{-16},\qquad
|\Im\beta_j(t)|\le|\Im t|/4,\qquad
|\gamma_j-\widehat\eta|\le2^{19}(E/\nu)\sqrt{q/\nu},
\quad\gamma_j>3/4\quad(t\in I).
\tag{LC377}
$$

The last inequality is restricted to real parameters.
The same fixed $C_{\rm ker}=2^{32}(1+128(S+3C_0)+C_0)$ pays this
for every $q\le C_0L$ and every larger $\nu$.
For $q=0$, $J=\widehat H\ne0$ gives no target node directly.
This gives an auxiliary-kernel certificate for complete local removal
without a local critical-line premise.

### The original convolution still needs its own sign information

The exact identities $C_t=\overline Q\boxplus_qR_{q,t}$,
$W_t=\overline Q\boxplus_qU_{q,t}$ and (LC308) survive because they
are algebraic and $\overline Q=Q_{\rm core}(c+z)$ has real
coefficients. Their sign consequences (LC314)--(LC316), (LC370)
do not follow merely from (LC377): those used the **real roots** of
$\overline Q$ for half-plane polarization and nonnegative weights.
Reality of its coefficients is not that hypothesis.

At a real actual $J$-node, with $R_j=R_{q,t}/(z-\beta_j)$, define
$a_j=(\overline Q\boxplus_qR_j)(\widehat\chi-c)$.
The existing linear convolution identities give, without dividing by
$\sum_ja_j$,

$$
J'(t)G(t)=\widehat H(t)^2
\left[\sum_j(\widehat\chi'-\beta_j')a_j\right]
\left[\sum_j\gamma_j a_j\right].
\tag{LC378}
$$

This is reuse of the signed cofactor interface, not an additional
joint lower bound. The cofactor signs, their common cancellation
and the case $\sum_ja_j=0$ remain unbounded. In particular,
$\gamma_j>0$ and $\widehat\chi'-\beta_j'>0$ alone do not decide this product.
A hyperbolic previous actual Jensen row at the first defect also
requires a separate relation to these same-source cofactors; it does
not imply real-rootedness of $Q_{\rm core}$ by definition.
No original-node nonreal exclusion, principal signed product,
all-degree Jensen hyperbolicity, RH, FIB arithmetic bridge or
all-integer Robin conclusion is supplied by (LC377) alone.

## A same-source infinite tower does not supply the missing cofactor sign

The auxiliary-kernel conclusion (LC377) and the original-node interface
(LC378) remain distinct even if the preceding actual Jensen rows are
hyperbolic. The following model preserves a whole source, its infinite
exterior zero set, strictly alternating nonzero coefficients, an arbitrarily
long zero-shift hyperbolic prefix, and every positive-shift hyperbolic row.
It nevertheless has a strictly negative response ratio at a simple node
immediately before its first nonreal-root defect. The model is not the
actual $\Xi$ source. It tests only whether these shared hypotheses supply
a universal transmission principle.

This is ordinary source-specific analytical exposition, without Lean or
mathematical-priority certification. The classical real-root and complex-zero
decreasing suppliers are reused. The added correspondence keeps the two
responses on the same infinite source and places their failure inside an
admissible full-growth chart.

### One fixed source for the entire tower

Fix $N\in\mathbb Z_{\ge2}$ and $c>0$. Set

$$
y=\frac{c}{\sqrt{N-1/2}}>0,\qquad C=c^2+y^2,\qquad
Q(z)=(z-c)^2+y^2,\qquad
B_\epsilon(z)=\frac{\sin\sqrt{\epsilon z}}{\sqrt{\epsilon z}},\qquad
f_\epsilon(z)=\frac{Q(z)}C B_\epsilon(z),\quad\epsilon>0.
\tag{LC379}
$$

The sinc expression denotes its entire power series, so no square-root
branch is selected. Its classical sine product is
$B_\epsilon(z)=\prod_{m\ge1}(1-z/\lambda_m)$ with
$\lambda_m=\pi^2m^2/\epsilon$. Thus $f_\epsilon$ is real entire of order
$1/2$, has the nonreal pair $c\pm iy$ and all these positive exterior
zeros, and satisfies $f_\epsilon(0)=1$. For fixed $N,c,\epsilon$, every
degree below uses this same function.

Write $b_j=\epsilon^j/(2j+1)!$ for $j\ge0$ and $b_j=0$ otherwise.
Then

$$
f_\epsilon(-z)=\sum_{j\ge0}a_jz^j,\qquad
a_j=b_j+\frac{2c}C b_{j-1}+\frac1C b_{j-2}>0.
\tag{LC380}
$$

Use the unchanged finite extraction
$\mathscr T_k h(t)=\sum_{j=0}^k(k)_{\underline j}h_jt^j/k^j$ for
$h(z)=\sum h_jz^j$, and define
$J_k=\mathscr T_k f_\epsilon$, $G_k=\mathscr T_k f_\epsilon'$ and
$q_k(x)=x^kJ_k(1/x)$. In particular,

$$
\begin{aligned}
q_k(0)&=(-1)^k k!a_k/k^k\ne0,\qquad \deg q_k=k,\qquad q_k\text{ monic},\\
q_k[h]&=h(\partial_x/k)x^k,\\
q_k[f_\epsilon]&=B_\epsilon(\partial_x/k)q_k[Q/C].
\end{aligned}
\tag{LC381}
$$

The differential series in (LC381) truncates on a polynomial. Its last
identity follows by multiplying the two constant-coefficient operators;
it uses all coefficients of the same source. The first line and coefficient
positivity exclude nonpositive real zeros of both $J_k$ and $q_k$. No
low-degree polynomial is being counted as a complete degree-$k$ row.

### A strict node before the first defect

At $\epsilon=0$, used only to compute a strict limit, $f_0=Q/C$. For
$k\ge2$ put $\delta_k=c^2-(1-1/k)C$. Direct extraction gives

$$
\begin{aligned}
CJ_k^{(0)}(t)&=(1-1/k)t^2-2ct+C,&
CG_k^{(0)}(t)&=2(t-c),\\
\delta_k&=\frac{c^2-(k-1)y^2}{k},&
\delta_N&=\frac{c^2}{N(2N-1)}>0,\qquad
\delta_{N+1}=-\frac{c^2}{(N+1)(2N-1)}<0.
\end{aligned}
\tag{LC382}
$$

For $k\le N$, the reflected polynomial $q_k[Q/C]$ has only real
zeros: for $k\ge2$ it is a real-root quadratic times $x^{k-2}$, while
$k=1$ is linear. For every $k>N$, it has exactly two nonreal zeros.
Let $d=\sqrt{\delta_N}$ and $t_-=(c-d)/(1-1/N)$. Since
$d<c/N$, this smaller simple root of $J_N^{(0)}$ is larger than $c$.
At this actual root,

$$
C(J_N^{(0)})'(t_-)=-2d<0,\qquad
CG_N^{(0)}(t_-)=2(t_--c)>0,\qquad
\frac{G_N^{(0)}(t_-)}{(J_N^{(0)})'(t_-)}
=-\frac1{1+\sqrt{2-1/N}}<-\frac13.
\tag{LC383}
$$

The two responses also obey the exact extraction identity
$(J_N^{(0)})'=G_N^{(0)}-(t/N)(G_N^{(0)})'$. Their opposite signs
were not obtained by assigning an independent adjacent polynomial.

### Restore every exterior zero without losing the real prefix

Bunton, Jacobs, Jenkins, McKenry, Piotrowski and Scott,
[*Non-Real Zero Decreasing Operators Related to Orthogonal Polynomials*,
arXiv:1312.2283v1](https://arxiv.org/html/1312.2283v1), Theorem 5,
recalls Piotrowski's Proposition 68. With its parameters
$(\alpha,\beta,c,d)=(1,0,0,-u)$ it states that $1-u\partial_x$
does not increase a real polynomial's number of nonreal zeros, counted
with multiplicity. The parameter called $c$ in that theorem is zero;
it is not the center in (LC379). All its sign conditions are satisfied.
Reuse that theorem for each factor in

$$
B_\epsilon(\partial_x/k)
=\lim_{M\to\infty}\prod_{m=1}^M
 \left(1-\frac{\epsilon}{k\pi^2m^2}\partial_x\right).
\tag{LC384}
$$

For fixed $k$, this is finite-dimensional coefficient convergence, with
the leading coefficient unchanged. If the limit had more nonreal roots
than the bound, disjoint small discs about its nonreal roots and the
classical continuity of polynomial roots would give the same excess in
the approximants. Thus (LC381)--(LC384) make every $q_k$, $k\le N$,
hyperbolic for every $\epsilon>0$, including the multiple-zero input at
$\epsilon=0$. No openness claim at those input multiple zeros is used.
For every $k$, the number of nonreal output roots is at most two.

At $k=N+1$, the nonreal simple pair of the limiting quadratic persists
for sufficiently small positive $\epsilon$. The exact same-source
derivative tower (LC159)--(LC160), applied to the nonzero coefficients
(LC380), makes its defect nondecreasing. Consequently, for a sufficiently
small fixed positive $\epsilon$,

$$
\Delta_k=
\begin{cases}0,&1\le k\le N,\\2,&k\ge N+1.\end{cases}
\qquad
\frac{G_N(t_\epsilon)}{J_N'(t_\epsilon)}<-\frac13
\quad\text{at a positive simple }J_N\text{ root }t_\epsilon\to t_-.
\tag{LC385}
$$

The last conclusion uses the simple-root continuation and strict margin
in (LC383); it evaluates both actual responses at the continued actual
root. It is not an approximate-node sign check.

### All positive-shift rows can also remain hyperbolic

Put $P_M(z)=\prod_{m=1}^M(1-z/\lambda_m)$ and
$f_M=(Q/C)P_M$. Choose $\epsilon$ additionally small enough that

$$
\lambda_1>4c,\qquad
\sum_{m\ge1}\frac1{\lambda_m-2c}<\frac{2c}C.
\tag{LC386}
$$

For example, when $\lambda_1\ge4c$ the sum is at most
$2\sum_m\lambda_m^{-1}=\epsilon/3$; hence these conditions can be
paid together. For every $M\ge1$, $f_M'(0)<0$ and
$f_M'(2c)/f_M(2c)=2c/C-\sum_{m=1}^M(\lambda_m-2c)^{-1}>0$.
Also $f_M'(\lambda_1)<0$. This places two distinct real roots of
$f_M'$ in $(0,2c)$ and $(2c,\lambda_1)$. Rolle's theorem supplies
$M-1$ more between consecutive exterior roots. Since
$\deg f_M'=M+1$, all its roots are positive and simple. Every higher
derivative remains real-rooted by Rolle, unless it is zero.

For a real-rooted polynomial $h$, the factorization of $h(\partial_x/k)$
into real linear differential factors, with any zero factors giving
ordinary derivatives, and the supplier above make
$h(\partial_x/k)x^k$ real-rooted or zero. Thus all finite Jensen rows
of $f_M^{(h)}$, $h\ge1$, are hyperbolic whenever nonzero. Letting
$M\to\infty$ preserves each fixed row by coefficient convergence.
For integers $h,k\ge1$, the leading coefficient is
$[t^k]\mathscr T_k f_\epsilon^{(h)}
=(-1)^{h+k}(h+k)!a_{h+k}/k^k\ne0$. Thus the limiting row
has its complete degree $k$. Therefore

$$
\mathscr T_k f_\epsilon^{(h)}\text{ is hyperbolic}
\quad\text{for every }h\ge1,\ k\ge1.
\tag{LC387}
$$

The same sufficiently small $\epsilon$ pays this whole family and
(LC385). Hyperbolicity of the adjacent response itself is therefore
insufficient to repair the strict current-node sign.

### The two actual kernel tangents fail on the same cofactors

At the strict limit $\epsilon=0$, the exterior is $A=1/C$ and
$H=\widehat H=1/C$, $\ell=s=0$, $\chi=t$ and $\eta=1$.
Use the same kernels as (LC305), at degree $n=N$ and core degree two:

$$
M_t(u)=e^{-tu}(1+tu/N)^N,\quad b_t(u)=u,\quad
R_{2,t}(z)=z^2-t^2/N,\quad U_{2,t}(z)=2z,\quad
\beta_\pm=\pm t/\sqrt N,\quad \beta_\pm'=\pm N^{-1/2},\quad
\gamma_\pm=1.
\tag{LC388}
$$

For $p=t_--c>0$ and $\sigma=t_-/\sqrt N$, the centered core is
$\overline Q(z)=z^2+y^2$ and the exact convolutions are
$C_t(z)=z^2+y^2-t^2/N$, $W_t(z)=2z$. At the actual node,
their cofactors and actual derivative weights are
$a_+=p+\sigma$, $a_-=p-\sigma$ and
$d_+=1-N^{-1/2}$, $d_-=1+N^{-1/2}$. Hence

$$
\sum_j\gamma_ja_j=2p>0,\qquad
\sum_jd_ja_j=2p-2t_-/N=-2d<0.
\tag{LC389}
$$

Even the frozen convolution $C_{t_-}$ has two simple real roots
$\pm p$. The failure is not a lack of real roots in that frozen output.
It is the opposite sign of the two correlated cofactor sums. This
realizes (LC378) without independent weights or a zero denominator.

### Arbitrarily large budgets do not exclude this thin-pair mechanism

Take $c=T^2$, $T\ge32$, $0<\rho\le1/8$, $D=T\rho$ and
$L=\log(T+2)$. Fix positive source-budget constants with $2\le C_0L$,
$E=128(S+3C_0)L$, and choose $N$ sufficiently large that

$$
\nu=N\rho^2/T^2\ge2^{32}(E+2),\qquad
\frac yD=\nu^{-1/2}\sqrt{\frac N{N-1/2}}<1,\qquad
0<t_--c<\frac c{N-1}<D/16.
\tag{LC390}
$$

Both nonreal roots belong to the core. Choose $\epsilon$ small enough
that every exterior height $\sqrt{\lambda_m}$ lies outside the complete
radius-$4\rho$ source selection. Thus $r=q=2$, all exterior zeros
remain in $A=B_\epsilon/C$, and the actual simple bad node lies in
the closed $D/16$ chart.

For these fixed parameters and each fixed $k$, $A\to1/C$,
$\mathscr T_kA\to1/C$ and $\mathscr T_k(A')\to0$
locally uniformly as $\epsilon\downarrow0$, while
$J_k\to\mathscr T_k(Q/C)$. On a larger closed
parameter disc their amplitudes are consequently nonzero, and Cauchy
estimates give convergence of the complete analytic jets with their
factorial/radius bounds. At the limit, the kernel labels in (LC388)
are explicit on that disc, their speed is $N^{-1/2}<2^{-16}$, and
$\gamma_\pm-\eta=0$. Continuation on a neighborhood of the closed disc
therefore retains their strict speed and positive-response budgets,
and any prescribed positive bound
$|\gamma_j-\eta|\le2^{19}(E/\nu)\sqrt{2/\nu}$, after choosing
$\epsilon$ sufficiently small. It also retains the full source jets,
nonzero amplitudes, infinite exterior zeros and the strict bad-node
ratio (LC385). This continuity argument fixes the chosen parameters
before selecting $\epsilon$; it does not identify the model's source
constants with those of $\Xi$.

In the source-height plane, $\tau_\pm=\sqrt{c\pm iy}$ have
$\Re\tau_\pm>T$ and

$$
|\tau_\pm-T|=\frac y{|\tau_\pm+T|}
<\frac{T}{2\sqrt{N-1/2}}.
\tag{LC391}
$$

To exclude this pair from the same-center closed radius-$4\rho$
selection requires $4\rho<|\tau_\pm-T|$, which forces
$\nu<N/[64(N-1/2)]<1/32$. This is incompatible with (LC390).
The strictly positive off-line width can tend to zero as $N$ grows.
Adaptive shrinking of the radius alone thus does not give a universal
way to avoid the pair while retaining the full-growth budget.

The construction rules out a universal first-defect bootstrap based only
on the preceding same-source hyperbolic rows, positive-shift hyperbolicity
and the auxiliary analytic/kernel certificate. It does not rule out an
additional relation specific to the actual theta coefficients of $\Xi$,
its finite extraction and its complete local/exterior factors. Such a
relation, the actual witness-location bridge and all-node coverage remain
unproved. No RH, FIB arithmetic or all-integer Robin conclusion follows.

### The model fails an unused positive-theta moment constraint

The actual normalized source has the original positive even theta measure
$d\mu(x)=\Phi(x)\,dx/\Xi(0)$, with the original normalization
$\Xi(t)=\int_{\mathbb R}\Phi(x)e^{itx}\,dx$ and
$F(z)=\Xi(\sqrt z)/\Xi(0)$. Its super-exponential tail permits
coefficient integration. If $F(-z)=\sum_{j\ge0}a_jz^j$, then

$$
\mu_j:=(2j)!a_j=\int_{\mathbb R}x^{2j}\,d\mu(x),\qquad
\mu_2^2\le\mu_1\mu_3.
\tag{LC392}
$$

The inequality directly reuses Cauchy--Schwarz for $x$ and $x^3$
in $L^2(\mu)$. Equivalently, these are moments of the pushforward
positive measure under $x\mapsto x^2$; no new moment theorem is claimed.
For the model (LC379)--(LC380), define its coefficient numbers by the
same factorial normalization, without asserting a positive measure.
At the strict limit $\epsilon=0$ they give

$$
\mu_1=4c/C,\qquad\mu_2=24/C,\qquad\mu_3=0,\qquad
\mu_1\mu_3-\mu_2^2=-576/C^2<0.
\tag{LC393}
$$

The first three coefficients are continuous in $\epsilon$ by (LC380).
For fixed $N,c$, every sufficiently small positive $\epsilon$ therefore
still violates (LC392). This requirement can be imposed together with
all the strict smallness conditions above. Thus this obstruction does
not preserve the actual positive-theta measure's joint moment constraints.

This diagnoses an additional source relation absent from the proposed
universal bootstrap; it does not supply the missing signed-cofactor
estimate. Neither this low-order constraint nor ordinary positive-measure
moment conditions have been shown to force the required sign when combined
with the actual first-defect and kernel hypotheses. The latter combined
implication remains a separate research question, with the complete
original source, its tails and every node retained.

### Positive moments and all positive shifts still leave a finite sign gap

The distinction in (LC392)--(LC393) does not by itself repair the node
sign. Reuse the classical cosine transform of a symmetric three-point
positive law, rather than claiming a new entire-function family. In the
unchanged extraction convention, take

$$
\mu=\frac7{11}\delta_0+\frac2{11}(\delta_{-1}+\delta_1),\qquad
f(z)=\frac{7+4\cos\sqrt z}{11},\qquad
f(-z)=1+\frac4{11}\sum_{j\ge1}\frac{z^j}{(2j)!}.
\tag{LC394}
$$

The square-root expressions mean their entire power series.
Then $f(t^2)=\int e^{itx}\,d\mu(x)$, and every coefficient
moment is genuinely the even moment $\mu_j=\int x^{2j}\,d\mu(x)$:
$\mu_0=1$ and $\mu_j=4/11$ for $j\ge1$.
Both ordinary and shifted Stieltjes Hankel matrices are positive
semidefinite. Indeed, their quadratic forms are integrals of a squared
polynomial, with an additional factor $x^2$ in the shifted case.
This uses the standard moment representation directly.

Set $J_k=\mathscr T_kf$, $G_k=\mathscr T_kf'$ as before. The first
three rows and the second-row derivative response are

$$
\begin{aligned}
J_1(t)&=1-2t/11,\\
132J_2(t)&=t^2-24t+132,\\
8910J_3(t)&=-t^3+90t^2-1620t+8910,\\
1320G_2(t)&=-240+40t-t^2.
\end{aligned}
\tag{LC395}
$$

The first two rows are hyperbolic with positive simple roots. The
monic cubic $-8910J_3$ has discriminant $-490106700<0$, hence
one real root and one nonreal conjugate pair. At the lower actual
second-row node $t_-=12-2\sqrt3>0$, use
$t_-^2=24t_--132$ to obtain

$$
J_2'(t_-)=-\sqrt3/33<0,\qquad
G_2(t_-)=(4t_--27)/330>0,\qquad
\frac{G_2(t_-)}{J_2'(t_-)}
=\frac{8\sqrt3-21}{10\sqrt3}<-\frac13.
\tag{LC396}
$$

The ratio uses both extractions of this same complete source.
Moreover, $f'(z)=-(2/11)\sin\sqrt z/\sqrt z$ has only positive
real zeros. Its sine-product partial products converge locally
uniformly. Their derivatives are real-rooted by Rolle's theorem,
and their finite Jensen extractions are real-rooted by the supplier
used in (LC384). Passing to each fixed derivative and extraction
preserves hyperbolicity. Every resulting row has degree $k$, since
its top coefficient is
$(-1)^{h+k}4(h+k)!/[11(2h+2k)!k^k]\ne0$ for $h,k\ge1$.
Consequently every positive-shift row $\mathscr T_kf^{(h)}$ is
hyperbolic, on this same positive-law source.

This is a parameter correspondence and direct application of classical
cosine, moment and real-root suppliers, without a priority or Lean claim.
It excludes a general finite-node implication using only positive-measure
moments, the preceding actual hyperbolic rows and all positive-shift rows.
It does not replace (LC379)--(LC391): the measure is atomic, its moment
matrices need not be positive definite, its source has infinitely many
nonreal pairs, and it does not supply that construction's arbitrarily
large full-growth budget or the original theta source's smooth density
and differential relations. No combined positive-theta/full-growth
counterexample or actual theta signed estimate is asserted.

## Strict positive moments still do not give a universal first-defect sign

The classical positive-law comparison in (LC394)--(LC396) can be
extended to strictly positive moment matrices and arbitrary prescribed
finite prefix length. This is a source-to-extraction correspondence
using classical Bessel, beta-integral and Laguerre suppliers, without
an originality or Lean claim. It does not impose the actual theta
density, complete original exterior or full-growth local budgets.

### One Bessel probability source supplies every positive shift

For $a>0$ and $b\ge1/2$, set

$$
B_b(z)={}_0F_1(;b;-z/4)
=\sum_{j\ge0}\frac{(-1)^jz^j}{4^j j!(b)_j},\qquad
f_{a,b}(z)=\frac{a+B_b(z)}{1+a},\qquad
P_{k,b}(t)=\frac{k!}{(b)_k}L_k^{b-1}(t/(4k)).
\tag{LC397}
$$

Here $(b)_j$ is the rising factorial. Reuse the Laguerre expression
in [DLMF 18.5.12](https://dlmf.nist.gov/18.5.E12).
[DLMF Table 18.3.1](https://dlmf.nist.gov/18.3#T1) supplies weight
$e^{-x}x^\alpha$ on $(0,\infty)$ for $\alpha>-1$. Here
$\alpha=b-1$ or $b+h-1$, both $>-1$. Reuse its zero theorem in
[DLMF 18.2(vi)](https://dlmf.nist.gov/18.2.vi). Directly applying the
unchanged coefficient multiplier gives, for integers $h,k\ge1$,

$$
\begin{aligned}
J_k&=\mathscr T_kf_{a,b}=(a+P_{k,b})/(1+a),\\
\mathscr T_kf_{a,b}^{(h)}(t)
&=\frac{(-1)^h}{(1+a)4^h(b)_h}
 \frac{k!}{(b+h)_k}L_k^{b+h-1}(t/(4k)).
\end{aligned}
\tag{LC398}
$$

Thus every positive-shift row has $k$ positive simple roots for this
one fixed source. The nonzero leading coefficients preserve complete
row degrees. No simultaneous perturbation of infinitely many rows
is used. For $b=1/2$, $B_b(z)=\cos\sqrt z$. For $b>1/2$, the beta
integral [DLMF 5.12.1](https://dlmf.nist.gov/5.12.E1) gives the even
probability density

$$
d\eta_b(x)=\frac{\Gamma(b)}{\sqrt\pi\Gamma(b-1/2)}
 (1-x^2)^{b-3/2}\mathbf1_{(-1,1)}(x)\,dx,\qquad
\nu_{a,b}=\frac{a}{1+a}\delta_0+\frac1{1+a}\eta_b.
\tag{LC399}
$$

Its even moments are $(1/2)_j/(b)_j$ before mixing, so
$f_{a,b}(t^2)=\int e^{itx}\,d\nu_{a,b}(x)$. Compact support gives
every square-exponential moment. For every nonzero real polynomial
$p$ and integer $\ell\ge0$, the density part makes
$\int x^{2\ell}p(x^2)^2\,d\nu_{a,b}>0$. Hence every finite matrix
$(\mu_{i+j+\ell})_{0\le i,j\le m}$ is positive definite, with
$\mu_j=\int x^{2j}\,d\nu_{a,b}$ and $m,\ell\ge0$.

The finite coefficient relation
$P_{n,b}=(n+b)P_{n,b+1}/b+4nP_{n,b}'$ yields at every actual
$J_n$ node

$$
G_n=\mathscr T_nf_{a,b}',\qquad
G_n(t)=\frac{n}{n+b}J_n'(t)
 +\frac{a}{4(1+a)(n+b)}\quad\text{if }J_n(t)=0.
\tag{LC400}
$$

The strictly positive second term is not removed by moment positivity.

### A rational node and a repeated node with strict moment matrices

Take $a=3/5$, $b=3/2$. Then
$f=(3+5\sin\sqrt z/\sqrt z)/8$ and
$\nu=(3/8)\delta_0+(5/8)U[-1,1]$. Its moments are
$\mu_0=1$, $\mu_j=5/[8(2j+1)]$ for $j\ge1$, and
$\mu_1\mu_3-\mu_2^2=1/336>0$. The first row has one positive
simple root, and

$$
\begin{aligned}
J_2(t)&=(t-16)(t-24)/384,\\
G_2(t)&=-5/48+t/96-t^2/5376,\\
J_2'(16)&=-1/48,\qquad G_2(16)=5/336,\qquad
G_2(16)/J_2'(16)=-5/7,\\
J_3(t)&=1-5t/48+t^2/288-t^3/36288.
\end{aligned}
\tag{LC401}
$$

The critical values of $J_3$ at $42\pm6\sqrt{14}$ are
$(17\pm4\sqrt{14})/24>0$. Thus the third row has one real root
and one nonreal pair: it is the first defect. All positive shifts
remain hyperbolic by (LC398). In the same $b=3/2$ family, taking
$a=2/3$ instead gives $J_2=(t-20)^2/400$ and
$G_2(20)=1/35\ne0$. Strict moment positivity therefore also does
not force a repeated node to be a common zero of the two responses.

### Arbitrarily long real prefixes and unbounded negative node ratios

Fix an integer $N\ge2$ and a real $M>0$. There are fixed parameters
$a>1$, $b>1/2$ for which $J_k$ has $k$ positive simple roots for
every $1\le k\le N$, $J_{N+1}$ is nonhyperbolic, and some actual
positive simple node of $J_N$ has $G_N/J_N'<-M$. The source also
has all the strict moment and positive-shift properties above.

To establish this, first take $b=1/2$ and write $P_n=P_{n,1/2}$.
For each integer $n\ge2$, let $u_n$ be its first positive critical point and
$A_n=-P_n(u_n)$. The classical Laguerre equation for
$y(x)=P_n(4nx)$ is
$xy''+(1/2-x)y'+ny=0$; see
[DLMF 18.8](https://dlmf.nist.gov/18.8). It implies

$$
\frac{d}{dx}\left(y^2+\frac{x}{n}(y')^2\right)
=\frac{2x}{n}(y')^2.
\qquad A_n>1,\qquad
 a+P_n\text{ is hyperbolic}\iff a\le A_n\quad(a>0).
\tag{LC402}
$$

Indeed, the energy strictly increases between consecutive critical
points, starting at $y(0)=1$. Interlacing of the positive simple
Laguerre roots and derivative roots therefore makes the first
negative minimum the smallest absolute extremal value. A horizontal
line at $-a$ meets all $n$ monotone intervals exactly when $a\le A_n$;
for $a<A_n$ all intersections are positive and simple.
The first row is handled separately: $J_1(t)=1-t/[4b(1+a)]$,
with one positive simple root for every $a>0$.

The existing reciprocal derivative tower gives $A_{n+1}\le A_n$.
The inequality is strict. At $a=A_n$, $J_n$ has a double root $u_n$,
while (LC400) gives $G_n(u_n)>0$. The existing exact adjacent-row
identity is
$J_{n+1}(u_n/\alpha_n)=J_n(u_n)+(u_n/n)G_n(u_n)>0$,
where $\alpha_n=n/(n+1)$. Thus the next reciprocal row has a repeated
derivative root at $\alpha_n/u_n$, but is nonzero there. This is
impossible for a real-rooted polynomial: each derivative zero away
from its roots is simple, by the strictly negative derivative of
its logarithmic derivative. Consequently $A_{n+1}<A_n$.

Choose $A_{N+1}<a<A_N$ and increase $a$ toward $A_N$.
At the first minimum's left node $t_-(a)$,
$P_N'(t_-(a))\to0^-$, and (LC400) gives

$$
\frac{G_N(t_-(a))}{J_N'(t_-(a))}
=\frac{N}{N+1/2}
 +\frac{a}{4(N+1/2)P_N'(t_-(a))}\longrightarrow-\infty.
\tag{LC403}
$$

Fix $a$ with ratio below $-M$. The finitely many simple real prefix
rows, the nonreal next row and the strict actual-node ratio persist
for one fixed $b>1/2$ sufficiently close to $1/2$ by coefficient and
simple-root continuity. All infinitely many positive shifts are
supplied directly by (LC398) for that fixed $b$. Formula (LC399)
then gives all strictly positive moment matrices. The parameter
conditions are open, so rational $a,b$ can also be selected.

This excludes a universal finite-node repair based only on strict
positive-law moments, arbitrarily long preceding actual hyperbolic
rows and all positive shifts. Each prescribed $N,M$ uses its own
fixed comparison source; no uniform source across all prefixes is
claimed. Nor is an exact two-root defect claimed for every $N+1$.
These laws have an atom at zero and a compactly supported density
component; they are not the original smooth theta law. Complete
original-source local/exterior budgets, the actual moving-band
location, all-node cofactor signs, RH and strict Robin remain unpaid.

## Atomless primitive sources retain positive shifts but not the zero row

This is a source-interface application of the classical beta/Bessel product,
Laguerre--Polya derivative closure and Jensen criterion. It is not a new
Bessel or Fourier theorem, a priority claim, Lean verification or an
actual-theta/RH counterexample. It addresses whether excluding the
zero-frequency atom and requiring Fourier decay repair the preceding
positive-law obstruction.

For real $c\ge64$, let $k_0(x)=(1-x^2)^5$ on $[-1,1]$, put
$k_c=k_0+2k_0''/c+k_0^{(4)}/c^2$ on this interval, and define

$$
p_c(x)=-k_c'(x)/x,\qquad
Z_c=\int_{-1}^1p_c(x)\,dx
=\frac{512(c^2-36c+504)}{63c^2}.
\tag{LC404}
$$

The quotient at zero has its polynomial extension. The probability law
has density $p_c/Z_c$ on $[-1,1]$ and zero density outside it.
It has no atoms. Its density is analytic in the open interval, but
is not claimed continuous at the support endpoints or smooth on the
whole real line.

Set $y=x^2$. The polynomial $p_c$ has the degree-eight Bernstein
expansion $\sum_{j=0}^8 b_j\binom8j y^j(1-y)^{8-j}$, with

$$
\begin{aligned}
(b_0,\ldots,b_8)=c^{-2}\bigl(&10(c^2-48c+720),\
5(c^2-36c+600),\
\tfrac{15}7(c^2-56),\\
&\tfrac57(c^2+120c-3024),\
\tfrac17(c^2+720c-21840),\\
&\tfrac{60}7(9c-350),\
\tfrac{120}7(2c-105),\
480,\ 3840\bigr).
\end{aligned}
\tag{LC405}
$$

Every coefficient is strictly positive for $c\ge64$. Thus $p_c>0$
on $[-1,1]$ and $Z_c>0$. In particular, if
$\mu_j=\int x^{2j}p_c(x)/Z_c\,dx$, then every finite matrix
$(\mu_{i+j+\ell})_{0\le i,j\le m}$ is strictly positive definite,
for all nonnegative $m,\ell$: its quadratic form is the integral
of $x^{2\ell}r(x^2)^2$ against a density positive on an interval.
All square-exponential moments are finite.

Define the entire source
$$
f_c(z)=Z_c^{-1}\int_{-1}^1p_c(x)\cos(x\sqrt z)\,dx.
\tag{LC406}
$$
The cosine means its entire power series in $z$. Thus $f_c(0)=1$,
$f_c(-z)$ has strictly positive coefficients, and $f_c$ has
order at most $1/2$. Riemann--Lebesgue gives $f_c(t)\to0$ for
real $t\to+\infty$.

Let
$$
B_b(z)={}_0F_1(;b;-z/4),\qquad
\kappa_c=\frac{c^2}{22(c^2-36c+504)}.
\tag{LC407}
$$
The beta integral and integration by parts give the exact SAME-source identity
$$
f_c'(z)=-\kappa_c(1-z/c)^2B_{13/2}(z).
\tag{LC408}
$$

Indeed, $k_0$ and its derivatives through order four vanish at the
support endpoints as needed. If $K_c(w)=\int k_c(x)e^{iwx}\,dx$,
then $K_c(w)=(1-w^2/c)^2K_0(w)$, while differentiating the
density transform gives $\frac{d}{dw}f_c(w^2)=-wK_c(w)/Z_c$.
The normalized $K_0$ is $B_{13/2}(w^2)$, and
$\int k_0=512/693$. This yields the displayed coefficient,
including its factor of two.

DLMF 10.21(i), 10.21.15 supplies the positive Bessel zeros and their
canonical product for order $11/2\ge0$. Consequently $B_{13/2}$
is Laguerre--Polya; multiplication by the real-rooted factor
$(1-z/c)^2$ preserves that class. Classical derivative closure
and the Jensen criterion therefore imply that
$\mathscr T_k f_c^{(h)}$ is hyperbolic for EVERY $h,k\ge1$,
on the same fixed $c$, where $J_k=\mathscr T_kf_c$,
$G_k=\mathscr T_kf_c'$, and the finite multiplier
$\mathscr T_kh=\sum_{j\le k}(k)_{\underline j}h_jt^j/k^j$
is unchanged. Its alternating, nonzero coefficients also exclude
nonpositive roots. No separate parameter is chosen for different
shifts or degrees; simplicity of all these shifted rows is not asserted.

The zero row is not forced into this class. Set
$$
H(c)=c^2Z_cf_c(c)=\int_{-1}^1c^2p_c(x)\cos(x\sqrt c)\,dx.
\tag{LC409}
$$
This extends to an entire function of $c$, because $c^2p_c$
is polynomial in $c$ and the cosine has an entire series.
It has $H(0)=4096\ne0$. Its positive real zeros are isolated,
so arbitrarily large $c$ avoid them. For every such $c$,
$$
f_c(c)\ne0,\qquad f_c'(c)=f_c''(c)=0.
\tag{LC410}
$$
If the nonconstant $f_c$ were Laguerre--Polya, its order below
one and positive $f_c(-t)$ would give a genus-zero product with
at least one positive root. Off its roots that product obeys
$$
(f_c'/f_c)'(c)=-\sum_r m_r/(c-r)^2<0.
\tag{LC411}
$$
The two vanishing derivatives instead make it zero, a contradiction.
Thus the classical Jensen criterion forces a nonhyperbolic finite
zero-shift row for every such $c$.

Moreover, as $c\to\infty$, the coefficients of $f_c$ converge
to those of $B_{11/2}$. The latter's finite zero-shift rows are
scaled $L_k^{9/2}$, with positive simple roots. For any prescribed
finite $N$, their stability supplies a threshold beyond which all
first $N$ rows of $f_c$ are also positive and simple. Choosing
one $c$ above that threshold with $H(c)\ne0$ gives a single
atomless positive source with an arbitrarily long normal prefix,
all positive-shift rows hyperbolic, and a later zero-shift defect.
This does not assert that the first defect is exactly $N+1$.

For the explicit parameter $c=64$, the probability density is
$$
\frac{45}{5248}(256x^8-448x^6+381x^4-274x^2+109),
\qquad -1\le x\le1.
\tag{LC412}
$$
It has $Z_{64}=41/9$ and $\kappa_{64}=256/3157$.
Exact rational coefficient extraction, square-free checks and
Sturm counts give $k$ positive simple roots for $1\le k\le12$,
and eleven positive simple roots for the degree-thirteen row.
Thus its first defect is thirteen, with two nonreal roots.
At the unique actual $J_{12}$ node in
$(131/2,6551/100)$, rational Sturm signs of $G_{12}$, $J_{12}'$,
$G_{12}+\frac75J_{12}'$ and $G_{12}+\frac32J_{12}'$ give
$$
-\frac32<\frac{G_{12}}{J_{12}'}<-\frac75.
\tag{LC413}
$$
The [exact source program and rational certificate](https://github.com/the-omega-institute/trureturing-experiments/tree/22e6d97d280e17e99117cbbf2e1d8457840085da/experiments/jensen-atomless-primitive)
retain the coefficient extraction, Bernstein check, square-free checks,
root counts and the four sign certificates on the same interval.
These are computed finite facts; the infinite positive-shift statement
and arbitrarily long-prefix result follow from the preceding suppliers
and argument, not from those finite counts.

The retained combination is stricter than adding a zero-frequency atom:
it preserves absolute continuity, every strictly positive moment packet,
all square-exponential moments, order at most $1/2$, Fourier decay,
every positive derivative-shift row and an arbitrarily long finite
zero-shift prefix. It does NOT preserve the actual theta density,
whole-real-line strict positivity or smoothness, theta's quantitative
Fourier decay, the actual Xi exterior, the full-growth parameter budget,
or the original moving-band witness. Therefore the actual-source
signed cofactor target and RH remain open; the new excluded generic
repair is only "remove atoms and impose Fourier decay".

## A smooth full-support version keeps the same infinite shifts

Retain the compact primitive source, its $c\ge64$, $k_c$,
$p_c=-k_c'/x$, $Z_c$ and $f_c$ from the preceding application.
Extend $k_c$ by zero outside $[-1,1]$. It is nonnegative, even,
continuous, absolutely continuous, strictly decreasing on $(0,1)$,
and has $k_c(\pm1)=0$. Its distributional derivative is the
ordinary function $-xp_c(x)\mathbf1_{[-1,1]}(x)$, with no boundary atom.

For $a>0$, let
$$
g_a(x)=\frac{e^{-a\cosh(2x)}}{K_0(a)},\quad
\widetilde k_{c,a}=k_c*g_a,\quad
\widetilde p_{c,a}(x)=-\widetilde k_{c,a}'(x)/x,\quad
\widetilde Z_{c,a}=\int_{\mathbb R}\widetilde p_{c,a}.
\tag{LC414}
$$
Here $K_\nu$ is the Macdonald function.
The exact integral $\int_{\mathbb R}e^{-a\cosh(2x)}dx=K_0(a)$
uses the published Macdonald integral; the divisor at zero takes
its smooth even extension. This $g_a$ is a whole probability law,
not separate smoothing for different rows.

For $x>0$,
$$
-\widetilde k_{c,a}'(x)
=\int_0^1t p_c(t)\,[g_a(x-t)-g_a(x+t)]\,dt>0,
\tag{LC415}
$$
since $g_a$ is strictly decreasing in $|x|$.
At zero its extension satisfies
$$
\widetilde p_{c,a}(0)
=-2\int_0^1t p_c(t)g_a'(t)\,dt>0.
\tag{LC416}
$$
Thus $\widetilde p/\widetilde Z$ is an everywhere positive,
even, smooth, atomless probability density on the whole real line.
Normalization is finite and positive. Each finite shifted square-moment
matrix is strictly positive definite, and all square-exponential
moments exist.

For fixed $c,a$, its tails obey
$$
\widetilde p_{c,a}(x)
\le C_{c,a}(1+e^{2|x|})
\exp[-(a/(2e^2))e^{2|x|}]
\quad(|x|\ge2).
\tag{LC417}
$$
This follows directly from $|t|\le1$,
$\cosh2(x-t)\ge e^{2(|x|-1)}/2$, the bound for $g_a'$,
and division by $|x|$. In particular, when $a>2\pi e^2$,
one may absorb the extra $e^{2|x|}$ in the stronger exponential
to obtain an upper tail $C_{c,a}\exp[-\pi e^{2|x|}]$.
This is a theta-scale upper tail, not equality with its actual density.

Define
$$
\widetilde f_{c,a}(z)
=\widetilde Z_{c,a}^{-1}\int_{\mathbb R}
\widetilde p_{c,a}(x)\cos(x\sqrt z)\,dx,\qquad
D_a(z)=\frac{K_{i\sqrt z/2}(a)}{K_0(a)}.
\tag{LC418}
$$
Both are entire in $z$, using the even Fourier power series.
The exact convolution/integration-by-parts calculation gives
$$
\widetilde f_{c,a}'(z)
=-\widetilde\kappa_{c,a}(1-z/c)^2B_{13/2}(z)D_a(z),
\qquad
\widetilde\kappa_{c,a}
=\frac{512/693}{2\widetilde Z_{c,a}}>0.
\tag{LC419}
$$

The classical Macdonald order-zero supplier is reused with argument
$a>0$ and order $i\sqrt z/2$: Sasaki, arXiv:1611.02467v2,
§2.1 and Theorem 3.1, (41), through the Dirichlet exponential
Schrödinger eigenvalue correspondence; Paris, arXiv:2108.01447v2,
(1.1) records the integral normalization. The Dirichlet spectrum
is positive and simple. Every complex order zero corresponds to
that same finite-norm eigenfunction, so its spectral square must
be positive real; this excludes nonreal $z$, not merely produces
a list of real zeros.
Explicitly, for any complex $K_\alpha(a)=0$, put
$y(s)=K_\alpha(ae^s)$. The reused Bessel equation and fixed-order
decay give a nonzero finite-norm Dirichlet eigenfunction. Integration
against its conjugate gives
$$
-\alpha^2=
\frac{\int_0^\infty(|y'|^2+a^2e^{2s}|y|^2)\,ds}
{\int_0^\infty|y|^2\,ds}>a^2.
\tag{LC420}
$$
For $D_a(z)$, $\alpha=i\sqrt z/2$, so $z=4(-\alpha^2)>0$.
This all-zero energy implication is distinct from Theorem 3.1's
assertion of infinitely many imaginary-order zeros.
 Superexponential decay bounds the square-variable
growth by $\exp[O(\sqrt{|z|}\log(|z|+2))]$, hence order at most $1/2$.
The nonzero normalized $D_a$ therefore has the genus-zero product
on its positive zeros and is Laguerre--Polya. These are the
source's classical spectral/Fourier properties, not a new
Hilbert--Pólya construction for Xi.

The product in the exact derivative is consequently Laguerre--Polya.
Derivative closure and the classical Jensen criterion give
$\mathscr T_k\widetilde f_{c,a}^{(h)}$ hyperbolic simultaneously
for every $h,k\ge1$. The smoothed source still has strictly alternating
nonzero coefficients. Its square-variable order is at most $1/2$.

There is also exponential Fourier decay. For fixed
$0<\eta<\pi/4$, shifting the contour of
$\widetilde p_{c,a}$ by $i\eta$ is justified: its possible
division singularity at zero is removable, $\cos(2\eta)>0$,
and the whole shifted density has integrable superexponential tails.
Thus
$$
|\widetilde f_{c,a}(w^2)|\le C_{c,a,\eta}e^{-\eta|w|}
\quad(w\in\mathbb R).
\tag{LC421}
$$
The exact critical rate $\pi/4$, its prefactor, lower asymptotics
and the theta modular identity are not asserted.

As $a\to\infty$, $g_a$ is an approximate identity and tends
to the point mass at zero. The resulting unnormalized density
converges locally away from the two original support endpoints;
its total mass and every fixed even moment converge to those of
$p_c$. One way to justify total-mass convergence without division
at zero is
$$
\int_{\mathbb R}\frac{-k'(x)}x\,dx
=2\int_0^\infty\frac{k(0)-k(x)}{x^2}\,dx.
\tag{LC422}
$$
Apply this to $k_c*g_a$, using a uniform second-derivative bound
near zero and the uniformly bounded $k_c$ elsewhere. Fixed moments
of positive order follow directly by integration by parts:
$\int x^{2j}(-k'/x)=(2j-1)\int x^{2j-2}k$.
For all $a\ge A>0$, the shifted compact-support convolution admits
a superexponential tail majorant uniform in $a$. It gives locally
uniform convergence of the transforms in $z$, including their
normalization, as $a\to\infty$.

Choose first a fixed $c$ for which the compact source has an arbitrary
prescribed number of initial simple positive rows and $f_c(c)\ne0$,
as supplied above. Then choose one sufficiently large finite $a$.
Coefficient/root stability retains those rows, and
$\widetilde f_{c,a}(c)\ne0$. The same exact derivative still gives
$\widetilde f'(c)=\widetilde f''(c)=0$, so the strict
genus-zero logarithmic derivative again excludes Laguerre--Polya
membership of the zero row. A later finite row must be nonhyperbolic.
No first-defect index is inferred merely from this existence argument.

For the compact parameter $c=64$, the preceding finite Sturm
certificate gives twelve simple positive initial rows, a simple
degree-thirteen defect and a simple actual $J_{12}$ node with
$-3/2<G_{12}/J_{12}'<-7/5$.
All these open finite conditions persist at ONE sufficiently large
finite $a$, including that actual moving root and its same-source
response. Hence there also exists a smooth everywhere positive,
full-support, atomless, theta-upper-tail source with exactly this
finite first-defect pattern and a negative actual response ratio,
while every positive shift remains hyperbolic.
No explicit finite $a$ threshold or numerical smooth-source
certificate is claimed.

This combined construction rules out the generic repair that adds
whole-real-line positivity/smoothness, absence of atoms, all
square-exponential moments, theta-scale upper tails, every subcritical
Fourier exponential-decay rate, all shifted moment positivity and all
positive-shift hyperbolicity to a long zero-row prefix. It does NOT
preserve the exact theta density, its modular/differential identity,
the actual Xi exterior, the original full-growth budget or the required
moving-band witness. The actual-source cofactor sign, RH, Robin and
the FIB arithmetic bridge remain unresolved. Ordinary source
applications and existence continuity are distinguished from the
finite exact compact-source computations; no Lean or priority claim
is made.

## Exact theta testing and the limit of a linear positive lift

The original source remains
$F(z)=\Xi(\sqrt z)/\Xi(0)$ and
$dP_\Phi(x)=\Phi(x)\,dx/\Xi(0)$ from Romik (1.6)--(1.11).
Use $\mathbb E=\mathbb E_\Phi$ and define, on this same full source,

$$
h(x)=-x\Phi'(x)/\Phi(x),\quad
k(x)=\Phi''(x)/\Phi(x),\quad
\tau(x)=\frac{\int_{|x|}^\infty y\Phi(y)\,dy}{\Phi(x)}.
\tag{LC423}
$$

For the unchanged $n\ge1,t>0,\mathscr T_n$, let

$$
B_{n,t}(x)=
\sum_{j=0}^n\frac{(-1)^j(n)_{\underline j}}{n^j(2j)!}t^jx^{2j}
={}_1F_1(-n;1/2;tx^2/(4n)).
\tag{LC424}
$$

Finite coefficient extraction, Fubini and integration by parts give

$$
J_n(t)=\mathbb EB_{n,t},\quad
G_n(t)=-\tfrac12\mathbb E[\tau B_{n,t}],\quad
2tJ_n'(t)=\mathbb E[(h-1)B_{n,t}].
\tag{LC425}
$$

Indeed
$\mathbb E[\tau X^{2j}]=\mathbb E[X^{2j+2}]/(2j+1)$;
combine this with
$(j+1)/(2j+2)!=1/[2(2j+1)(2j)!]$ for $G_n$.
Also $x\partial_xB=2t\partial_tB$.
These identities use $G_n=\mathscr T_nF'$, not $G_n=J_n'$.
The exact Laguerre differential equation, with
$\alpha_t=t/(2n)$, is
$B''-\alpha_t xB'+tB=0$.
At an actual node $\mathbb EB=0$, it yields
$\mathbb E[(k-\alpha_t h)B]=0$, and

$$
J_n'(t)G_n(t)
=-\frac1{4t}\mathbb E[hB_{n,t}]\mathbb E[\tau B_{n,t}].
\tag{LC426}
$$

All boundary terms vanish by the original theta tail. This is an
exact parameter correspondence: $\alpha_t=(t/T^2)\rho^2/(2\nu)$
in the existing local height variables. At the real actual nodes of
LC378, its signed cofactor product is precisely the last expression
divided by $\widehat H(t)^2$. No exterior, multiplicity, nonreal
core zero or response is discarded. The representation itself pays
no new sign bound.

It does, however, permit a source-faithful test of a proposed *linear*
positive lift. For any fixed finite $\alpha>0$, let

$$
\mathcal V_\alpha=
\{b\in L^2_{\mathrm{even}}(P_\Phi;\mathbb R):
\mathbb Eb=0,\ \mathbb E[(k-\alpha h)b]=0\},
\quad
\mathcal Q_\Phi(b)=-\mathbb E[hb]\mathbb E[\tau b].
\tag{LC427}
$$

The form $\mathcal Q_\Phi$ on this actual-source space has both
strictly positive and strictly negative directions. To see this,
the complete original series and its first-summand tail give

$$
h(x)\sim2\pi xe^{2x},\qquad
k(x)\sim4\pi^2e^{4x},\qquad
\tau(x)\sim x/(2\pi e^{2x})\to0
\quad(x\to+\infty).
\tag{LC428}
$$

For the first two expressions, differentiate the normally convergent
original theta series, retaining the exponentially smaller summands;
do not differentiate an unbounded asymptotic remainder. For the
third, compare the tail integral with
$x\Phi(x)/(2\pi e^{2x})$ by the derivative-ratio limit.
The same tail shows these three functions belong to $L^2(P_\Phi)$.
They are smooth, $\tau>0$, and
$1,h,k,\tau$ are linearly independent: successively compare the
$e^{4x}$, $xe^{2x}$, constant and vanishing positive terms.
Almost-everywhere equality here becomes pointwise equality because
the actual density is positive and the functions are continuous.

Let $P_\alpha$ be orthogonal projection onto $\mathcal V_\alpha$,
$u=P_\alpha h$, $v=P_\alpha\tau$. Independence implies
$u,v$ are nonzero and independent: any relation would put
a combination of $h,\tau$ in
$\operatorname{span}\{1,k-\alpha h\}$.
Set $\zeta=\langle u,v\rangle/(\|u\|\|v\|)\in(-1,1)$ and
$b_\pm=u/\|u\|\pm v/\|v\|$. Then

$$
\mathcal Q_\Phi(b_+)=-\|u\|\|v\|(1+\zeta)^2<0,\qquad
\mathcal Q_\Phi(b_-)=\|u\|\|v\|(1-\zeta)^2>0.
\tag{LC429}
$$

Thus no linear lifting $L$ and positive operator $A$ can
represent this exact form as
$\langle Lb,ALb\rangle$ for *every*
$b\in\mathcal V_\alpha$. The common kernel of the two response
functionals inside this infinite-dimensional space also contains
nonzero vectors. This stronger linear relaxation supplies neither
strict sign nor common-zero exclusion.

These are classical integration, Laguerre and projection suppliers
applied to the actual theta source. The added inference excludes only
the proposed lift on the whole linear root-and-curvature constraint
space. It is not a negative actual Jensen-node witness: the displayed
$b_+$ need not be $B_{n,t}$ or satisfy its full differential
equation/coefficient recurrence. Those nonlinear actual-test
restrictions and all previous-row real-root conditions must still
be used. No implication about the sign on those actual tests is
inferred from indefiniteness of their larger containing space.

The same first-defect source, moving-band localization, actual
cofactor/common-zero control and Robin's complete same-clock signed
response remain unpaid. No Lean, original-source node counterexample,
mathematical-priority, RH or strict all-integer Robin claim is made.
