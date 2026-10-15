# Actual fixed-pole strict ground-energy gap in the native cylinder

> This volume uses the `generic-v1` definition/theorem/proof format.
> Its results are ordinary handwritten mathematics under the explicit
> inherited analytic contract below. The comparison concerns actual
> attained minima of one point-source form and its base restriction.

## 1. One native realization and its inherited analytic contract

**Definition 1.1 (native parameters, coordinates and clock).** Fix

$$
0<Z<1,\qquad r=1-Z,\qquad h=r/2,\qquad
I=(l,u)\Subset(0,h),\qquad d=u-l>0,\qquad \varepsilon>0.
\tag{1.1}
$$

The original double-wall probabilities, in mode order $(0,1,2,3,13)$,
are $(k,h-k,Z,h-k,k)$, with $X=Y=h$ and $0<k<h$.
The preparation height is any fixed member of $(0,h)$ and the preparation
phases are arbitrary and fixed. In the phase convention
$\psi_s=\sqrt{p_s}e^{-i\theta_s}$, the native torus coordinates are

$$
\alpha=u_0-v_0\pmod{2\pi},\qquad
\beta=u_0\pmod{2\pi},\qquad
(u_0,v_0)=(\beta,\beta-\alpha).
\tag{1.2}
$$

Both circles have period $2\pi$. The source manifold and its base are
$(0,h)\times\mathbb T_\alpha\times\mathbb T_\beta$ and
$(0,h)\times\mathbb T_\alpha$, respectively, with
$\pi(k,\alpha,\beta)=(k,\alpha)$. On the analytic cylinders use

$$
\begin{gathered}
\Omega=I\times\mathbb T_\alpha\times\mathbb T_\beta,
\qquad D=I\times\mathbb T_\alpha,\qquad
\mathbb T=\mathbb R/(2\pi\mathbb Z),\\
\mu=dk\,d\alpha\,d\beta,\qquad \nu=dk\,d\alpha,\\
P=\partial_k,\qquad Q=\tfrac12\partial_\alpha+c(k)\partial_\beta,
\qquad c(k)=\tfrac12-k/r.
\end{gathered}
\tag{1.3}
$$

The angular measures are unnormalized Haar measures. The density is one.
The free covariance is $2\operatorname{diag}(\varepsilon^2,1)dt$ in
the two original control directions, and killing occurs on first height
exit from $I$. This is the clock of [Q, Definitions 1.1--1.3], with no
change of angular period or additional hidden-phase actuator. The
amplitudes below are functions on this cylinder; their preparation by
native controls is not an assumption or a conclusion.

**Definition 1.2 (full horizontal form and base restriction).** Inner
products are linear in their first argument. Put

$$
\begin{aligned}
T(f,z)&=\int_\Omega
 \bigl(\varepsilon^2(Pf)\overline{Pz}+(Qf)\overline{Qz}\bigr)d\mu,
&T[f]&=T(f,f),\\
\mathcal F&=\overline{C_c^\infty(\Omega)}^{(\|\cdot\|_2^2+T)^{1/2}},\\
\overline T(v,z)&=\int_D
 \bigl(\varepsilon^2v_k\overline{z_k}+\tfrac14v_\alpha
 \overline{z_\alpha}\bigr)d\nu,
&\overline T[v]&=\overline T(v,v),\\
\overline{\mathcal F}&=
 \overline{C_c^\infty(D)}^{(\|\cdot\|_2^2+\overline T)^{1/2}}.
\end{aligned}
\tag{1.4}
$$

Compact support concerns height; all angular functions are periodic.
The full domain $\mathcal F$ is exactly the horizontal Dirichlet closure
in (1.4). No identification with isotropic $H^1_0(\Omega)$ is made.
The base domain is the usual $H^1$ space on $D$ with zero height trace
and periodic angle, because $\varepsilon$ is fixed and positive.

Write $L$ and $\overline L$ for the nonnegative form operators. Thus, for
example,

$$
\begin{aligned}
D(\overline L)=\{v\in\overline{\mathcal F}:\ &\exists F\in L^2(D,\nu),
\ \overline T(v,z)=\langle F,z\rangle
\text{ for every }z\in\overline{\mathcal F}\},\\
\overline Lv&=F.
\end{aligned}
\tag{1.5}
$$

Use the isometry and projection

$$
Jv=\frac{v(k,\alpha)}{\sqrt{2\pi}},\qquad
J^*f=\frac1{\sqrt{2\pi}}\int_{\mathbb T}f\,d\beta,\qquad
\Pi=JJ^*=\frac1{2\pi}\int_{\mathbb T}(\,\cdot\,)d\beta.
\tag{1.6}
$$

**Contract 1.3 (inherited analytic premises and exact correspondence).**
The mathematical reference [Q] is *Native observation quotient, hidden
Green harmonics and attractive response*. The following are the inherited
facts about the singular native realization. They are stated explicitly
so that no result about an unopened supplier is an additional premise.

1. [Q, Definition 1.3] supplies a strictly positive smooth free heat
   kernel $p_t^\Omega$ for $e^{-tL}$, a positive free spectral gap and
   compact free resolvent. For the fixed original point
   $o=(k_o,\alpha_o,\beta_o)\in\Omega$, its Green field is

   $$
   \Gamma_o(q)=\int_0^\infty p_t^\Omega(o,q)\,dt.
   \tag{1.7}
   $$

   It is positive, integrable on $\Omega$, smooth and finite off $o$,
   and infinite at $o$. Its unit-source normalization is
   $\int_\Omega\Gamma_o L\varphi\,d\mu=\varphi(o)$ for compact smooth
   tests. This full infinite-time field is used in every full energy.

2. [Q, Theorem 2.1] supplies the closed-domain free reduction

   $$
   \begin{gathered}
   \Pi\mathcal F\subset\mathcal F,\qquad
   \mathcal F\cap\operatorname{Ran}J=J\overline{\mathcal F},\qquad
   T[Jv]=\overline T[v],\\
   T(\Pi f,(1-\Pi)z)=0\quad(f,z\in\mathcal F),\qquad
   e^{-tL}J=Je^{-t\overline L}.
   \end{gathered}
   \tag{1.8}
   $$

   In the normalized base eigenbasis

   $$
   e_{jm}(k,\alpha)=\sqrt{\frac2d}
    \sin\frac{j\pi(k-l)}d\,\frac{e^{im\alpha}}{\sqrt{2\pi}},
   \qquad \lambda_{jm}=\varepsilon^2(j\pi/d)^2+m^2/4,
   \tag{1.9}
   $$

   where $j\ge1$ and $m\in\mathbb Z$, the form and operator domains
   are respectively $\sum\lambda_{jm}|v_{jm}|^2<\infty$ and
   $\sum\lambda_{jm}^2|v_{jm}|^2<\infty$.

3. [Q, Definition 2.2 and Theorem 3.1] supplies the base heat product,
   the same height killing and the exact hidden marginal. With
   $x_o=(k_o,\alpha_o)=\pi o$,

   $$
   \begin{aligned}
   \overline p_t(x_o,(k,\alpha))
      &=h_t^I(k_o,k)s_t(\alpha-\alpha_o),\\
   h_t^I(k_o,k)&=\frac2d\sum_{j\ge1}
     e^{-\varepsilon^2(j\pi/d)^2t}
     \sin\frac{j\pi(k_o-l)}d\sin\frac{j\pi(k-l)}d,\\
   s_t(a)&=\frac1{2\pi}\sum_{m\in\mathbb Z}e^{-m^2t/4}e^{ima},\\
   \overline\Gamma_{x_o}(x)&=\int_0^\infty\overline p_t(x_o,x)dt,
   \qquad
   W(x)=\frac{\overline\Gamma_{x_o}(x)}{2\pi}
        =\frac1{2\pi}\int_{\mathbb T}\Gamma_o(x,\beta)d\beta.
   \end{aligned}
   \tag{1.10}
   $$

   The extended value $W(x_o)$ is infinite. The corresponding heat marginal is
   $\int_{\mathbb T}p_t^\Omega(o,(x,\beta))d\beta
   =\overline p_t(x_o,x)$. It holds for every source point and every
   positive time. Consequently the base kernel is strictly positive
   at every pair of interior points. The height process has generator
   $\varepsilon^2\partial_k^2$ and is killed on leaving $I$.
   The full Green height marginal is the pointwise identity

   $$
   \int_{\mathbb T^2}\Gamma_o(k,\alpha,\beta)d\alpha d\beta
    =\varepsilon^{-2}G_I(k_o,k),\qquad
   G_I(a,k)=\frac{(\min(a,k)-l)(u-\max(a,k))}{d}.
   \tag{1.11}
   $$

4. [Q, Definition 3.2, equation (3.7)] supplies constants $C_H>0$ and
   $0\le B_\varepsilon<\infty$ for this fixed realization such that

   $$
   V_o[f]:=\int_\Omega\Gamma_o|f|^2d\mu
   \le\frac{2rC_H}{\varepsilon^2}T[f]
      +B_\varepsilon\|f\|_2^2
   \qquad(f\in\mathcal F).
   \tag{1.12}
   $$

   In particular $V_o[f]$ is finite on the original full form domain.
   This supplied bound, rather than a new Hardy surrogate potential,
   controls the actual point-source multiplier.

The source's first-harmonic theorem is restated with its normalization
argument in Lemma 5.1 below. Closedness and attainment are deduced here
from the displayed bound and compactness. Standard Hilbert-space
compactness, weak lower semicontinuity of a Hilbert norm, the Sobolev
chain rule, Fourier/Parseval identities and the elementary integral and
sequence inequalities used below have their usual meanings. None is an
additional assumption about the singular full attractive operator.

**Definition 1.4 (strict stable coupling and actual infima).** Fix

$$
g=\gamma\varepsilon^2,\qquad
0<\gamma<(2rC_H)^{-1},\qquad
\theta=2rC_H\gamma<1.
\tag{1.13}
$$

On precisely the domains in (1.4) define

$$
\begin{aligned}
q_g(f,z)&=T(f,z)-g\int_\Omega\Gamma_of\overline z\,d\mu,
&q_g[f]&=q_g(f,f),\\
\overline q_g(v,z)&=\overline T(v,z)-g\int_D Wv\overline z\,d\nu,
&\overline q_g[v]&=\overline q_g(v,v),\\
E_{\rm full}&=\inf_{f\in\mathcal F,\ \|f\|_2=1}q_g[f],
&E_{\rm base}&=\inf_{v\in\overline{\mathcal F},\ \|v\|_2=1}
                  \overline q_g[v].
\end{aligned}
\tag{1.14}
$$

Tonelli, (1.6) and (1.10) give

$$
V_o[Jv]=\int_D W|v|^2d\nu,\qquad
q_g[Jv]=\overline q_g[v].
\tag{1.15}
$$

Weighted Cauchy--Schwarz and (1.12) give the sesquilinear identities as
well. Thus $E_{\rm base}$ is the restriction of the very same fixed-pole
form. The factor $1/(2\pi)$ in $W$ is forced by the isometric lift.
The full problem continues to contain $\Gamma_o$, not $W\circ\pi$.
No negative-binding inequality is imposed.

## 2. Finite actual minima and a nonnegative restricted minimizer

**Theorem 2.1 (strict coercivity, closed forms and attainment).** Under
Definitions 1.1--1.4 both infima in (1.14) are finite attained minima.
The forms are closed and semibounded on exactly their declared domains.
In particular

$$
-gB_\varepsilon\le E_{\rm full}\le E_{\rm base}<\infty.
\tag{2.1}
$$

Proof. From (1.12), positivity of $\Gamma_o$ and (1.13),

$$
(1-\theta)T[f]-gB_\varepsilon\|f\|_2^2
 \le q_g[f]\le T[f].
\tag{2.2}
$$

For $\kappa=gB_\varepsilon+1$ this gives

$$
(1-\theta)T[f]+\|f\|_2^2
 \le q_g[f]+\kappa\|f\|_2^2
 \le T[f]+\kappa\|f\|_2^2.
\tag{2.3}
$$

The middle expression is a positive definite quadratic form whose norm
is equivalent to the complete free form norm on $\mathcal F$. The
potential sesquilinear form is continuous in that norm, since

$$
\left|\int_\Omega\Gamma_of\overline z\,d\mu\right|
 \le V_o[f]^{1/2}V_o[z]^{1/2}.
\tag{2.4}
$$

It follows that the shifted form is a Hilbert norm on the same vector
space, proving closedness and the lower bound. Equations (1.8) and
(1.15) give exactly the same statements for the base form.

The full free form domain embeds compactly into $L^2(\Omega)$ by the
inherited compact free resolvent. Equivalently, the spectral calculus of
$L$ writes this embedding as $(1+L)^{-1/2}$ from an $L^2$ space; this
operator is compact because the free resolvent is compact. On the base,
the eigenvalues (1.9) tend to infinity with $j^2+m^2$, so the same
compactness follows directly by truncating the coefficient expansion.
Equivalence (2.3) preserves both compact embeddings for the shifted forms.

Each unit sphere has nonzero smooth members with finite energy by
(1.12); hence its infimum has a finite upper bound. It has lower bound
$-gB_\varepsilon$ by (2.2). A normalized minimizing sequence is bounded
in the shifted form norm by (2.3). It has a weakly convergent subsequence
in that Hilbert space and a strongly convergent subsequence in $L^2$.
The two limits coincide, and the strong limit still has norm one. Weak
lower semicontinuity of the shifted norm, followed by the strong
$L^2$ convergence of the shift term, proves attainment. This argument
applies to both forms. Finally the isometry $J$ and (1.15) give the
middle inequality in (2.1). No sign of a trial energy was used. $\square$

**Lemma 2.2 (modulus minimizer and weak eigen-equation).** There exists a
real nonnegative $v\in\overline{\mathcal F}$ with

$$
\|v\|_2=1,\qquad \overline q_g[v]=E_{\rm base}=:E,
\qquad
\overline q_g(v,z)=E\langle v,z\rangle
\quad(z\in\overline{\mathcal F}).
\tag{2.5}
$$

The modulus of any normalized restricted minimizer has these properties.

Proof. Start with a complex minimizer $u$ from Theorem 2.1. The
regularized modulus
$F_\tau(u)=\sqrt{|u|^2+\tau^2}-\tau$ has zero height trace and obeys
the weak derivative inequalities
$|\partial_kF_\tau(u)|\le|\partial_ku|$ and
$|\partial_\alpha F_\tau(u)|\le|\partial_\alpha u|$.
These follow by applying the chain rule to the two real components of
$u$; the differential of $F_\tau$ has norm at most one.
As $\tau\downarrow0$ these functions converge to $|u|$ in $L^2$ and
are bounded in the base Sobolev norm. Weak compactness and lower
semicontinuity therefore give

$$
v=|u|\in\overline{\mathcal F},\qquad
\overline T[v]\le\overline T[u].
\tag{2.6}
$$

The norm and potential integral are unchanged by the modulus, so
minimality forces $\overline q_g[v]=E$ and $\|v\|_2=1$.
For every $z$ differentiate the Rayleigh quotient of $v+tz$ at $t=0$.
Real $t$ gives the real part of (2.5); replacing $z$ by $iz$ gives its
imaginary part. All pairings are continuous by (2.4) and its restriction.
This establishes the weak equation on the whole form domain. $\square$

## 3. Logarithmic base-pole control and the Sobolev bridge

**Lemma 3.1 (the actual marginal belongs to every finite $L^p$).** Put

$$
\rho(k,\alpha)=
 \bigl((k-k_o)^2+\operatorname{dist}_{\mathbb T}(\alpha,\alpha_o)^2\bigr)^{1/2}.
\tag{3.1}
$$

For some finite constant $C$ depending on the fixed realization,

$$
0\le W(k,\alpha)
 \le C\left(1+\log_+\frac1{\rho(k,\alpha)}\right)
 \quad\text{if }(k,\alpha)\ne x_o.
\tag{3.2}
$$

Consequently $W\in L^p(D,\nu)$ for every $1\le p<\infty$.
The extended Green value at $x_o$ is infinite, as in [Q, Theorem 3.1];
that single value has no effect on these $L^p$ statements. Moreover
$W$ is smooth off $x_o$.

Proof. The killed height transition measure is bounded by the unrestricted
height Brownian transition measure. By the supplied height generator and
continuity of the densities this gives, for $t>0$,

$$
0\le h_t^I(k_o,k)\le
 \frac1{\sqrt{4\pi\varepsilon^2t}}
 \exp\left(-\frac{(k-k_o)^2}{4\varepsilon^2t}\right).
\tag{3.3}
$$

The wrapped Gaussian is exactly the circle heat kernel of (1.10):

$$
s_t(a)=\frac1{\sqrt{\pi t}}
 \sum_{n\in\mathbb Z}\exp\left(-\frac{(a+2\pi n)^2}{t}\right).
\tag{3.4}
$$

Indeed its $m$-th Fourier coefficient, with the coefficient convention
$(2\pi)^{-1}\int_{-\pi}^{\pi}s_t(a)e^{-ima}da$, is
$(2\pi)^{-1}e^{-m^2t/4}$, by combining the translated Gaussian
integrals on the real line. Absolute convergence and the Fourier
uniqueness identity give (3.4).

Choose $a\in[-\pi,\pi]$ representing $\alpha-\alpha_o$. For $n\ne0$
one has both $|a+2\pi n|\ge|a|$ and
$|a+2\pi n|\ge\pi|n|$. Therefore, for $0<t\le1$,

$$
\sum_{n\in\mathbb Z}e^{-(a+2\pi n)^2/t}
 \le e^{-a^2/(2t)}
   \left(1+2\sum_{n\ge1}e^{-\pi^2n^2/(2t)}\right)
 \le C_0e^{-a^2/(2t)}
\tag{3.5}
$$

with $C_0<\infty$. Combining (3.3)--(3.5) with the exact heat product
gives constants $M_{\rm heat},a_{\rm heat}>0$ such that

$$
\overline p_t(x_o,x)\le M_{\rm heat}t^{-1}e^{-a_{\rm heat}\rho(x)^2/t}
\quad(0<t\le1).
\tag{3.6}
$$

For $t\ge1$ the absolute sine and circle series in (1.10) instead give

$$
\overline p_t(x_o,x)\le
 C_2e^{-\lambda_{10}t},\qquad
\lambda_{10}=\varepsilon^2\pi^2/d^2>0,
\tag{3.7}
$$

uniformly in $x$. For example, factor $e^{-\lambda_{10}t}$ out of the
height sum and bound the remaining sum at $t=1$; the circle absolute
sum is also bounded at $t=1$.

If $0<\rho\le1$, split the small-time integral in (3.6) at $t=\rho^2$.
The substitution $s=\rho^2/t$ on the first part gives

$$
\int_0^{\rho^2}t^{-1}e^{-a_{\rm heat}\rho^2/t}dt
 =\int_1^\infty\frac{e^{-a_{\rm heat}s}}s\,ds<\infty,
\qquad
\int_{\rho^2}^1\frac{dt}{t}=2\log\frac1\rho.
\tag{3.8}
$$

For $\rho\ge1$ the same small-time integral has a uniform finite
bound. Equation (3.7) bounds the entire large-time integral.
Dividing by $2\pi$ as in (1.10) proves (3.2).
In a small base coordinate disk around $x_o$, for each finite $p$,

$$
\int_0^a s(1+|\log s|)^pds<\infty.
\tag{3.9}
$$

Outside that disk (3.2) is bounded, and $D$ has finite measure. This
proves the $L^p$ assertion. Finally, over a compact base neighborhood
not containing $x_o$, its product with the hidden circle is a compact
set not containing $o$. The full field is smooth there by Contract 1.3.
Differentiation under the compact hidden integral in (1.10) proves
smoothness of $W$ on that neighborhood. $\square$

**Lemma 3.2 (the needed two-dimensional Sobolev estimate).** For a finite
constant $C_S$ depending on $I$ and the fixed $\varepsilon$,

$$
\|z\|_{L^4(D)}\le C_S
 \bigl(\|z\|_2^2+\overline T[z]\bigr)^{1/2}
 \qquad(z\in\overline{\mathcal F}).
\tag{3.10}
$$

Proof. Odd reflection at the two zero-trace height faces extends $z$ to
an $H^1$ function on a torus of height period $2d$ and angular period
$2\pi$, with a bounded extension norm. For Fourier coefficients $a_n$
on that torus, $n\in\mathbb Z^2$, put $w_n=1+|n|^2$; the fixed
periods only change comparison constants. Hölder gives

$$
\sum_n|a_n|^{4/3}
 \le\left(\sum_n w_n|a_n|^2\right)^{2/3}
      \left(\sum_n w_n^{-2}\right)^{1/3}.
\tag{3.11}
$$

The last sum is finite in two dimensions, by comparison with the
integral of $(1+|\xi|^2)^{-2}$. For a trigonometric polynomial $U$,
Parseval for $U^2$ and Young's sequence convolution inequality give

$$
\|U\|_4^2=\|U^2\|_2
 \le C\|a*a\|_{\ell^2}
 \le C\|a\|_{\ell^{4/3}}^2
 \le C'\sum_nw_n|a_n|^2.
\tag{3.12}
$$

The constants include only Fourier normalization and periods. Apply
(3.12) to differences of Fourier polynomials approximating the extension
in $H^1$. They converge in $L^4$, with the same $L^2$ limit, proving
the inequality for the extension. Restrict to $D$ and use equivalence
of the base form norm with $H^1$ to obtain (3.10). No $H^1$ to
$L^\infty$ embedding is used. $\square$

## 4. Regularity and positivity of the actual restricted ground state

**Theorem 4.1 (weak free-domain bridge and regularity).** Every
nonnegative normalized minimizer $v$ in Lemma 2.2 satisfies

$$
Wv\in L^2(D),\qquad v\in D(\overline L),\qquad
\overline Lv=(E+gW)v\quad\text{in }L^2(D).
\tag{4.1}
$$

It has a continuous representative on $[l,u]\times\mathbb T$, equal
to zero on the two height faces, belongs to $H^2(D)$, and is smooth on
$D\setminus\{x_o\}$.

Proof. Lemma 3.1 gives $W\in L^4$ and Lemma 3.2 gives $v\in L^4$.
Hölder therefore yields $\|Wv\|_2\le\|W\|_4\|v\|_4<\infty$.
The weak equation (2.5) becomes

$$
\overline T(v,z)=\langle(E+gW)v,z\rangle
\quad\text{for every }z\in\overline{\mathcal F}.
\tag{4.2}
$$

Its right side has an $L^2$ representative. Definition (1.5), not an
assumed intersection formula for an attractive operator domain, now
proves (4.1).

By the inherited exact operator-domain description (1.9),
$\sum\lambda_{jm}^2|v_{jm}|^2<\infty$.
For these fixed positive parameters and $j\ge1$, $\lambda_{jm}$ is
bounded above and below by positive multiples of $1+j^2+m^2$.
The sine/Fourier expansion, or its odd periodic extension in height,
thus gives all second weak derivatives in $L^2$, proving $H^2$.
Furthermore

$$
\sum_{j,m}|v_{jm}|
 \le\left(\sum_{j,m}\lambda_{jm}^2|v_{jm}|^2\right)^{1/2}
      \left(\sum_{j,m}\lambda_{jm}^{-2}\right)^{1/2}<\infty.
\tag{4.3}
$$

The basis functions $e_{jm}$ are uniformly bounded on the closed
cylinder. Hence the series converges absolutely and uniformly there.
Its sum is continuous, represents $v$, and vanishes at both height
faces, since each sine does.

For local smoothness choose a smooth cutoff $\zeta$ supported in
$D\setminus\{x_o\}$ and away from the height faces. Here $W$ is
smooth by Lemma 3.1. In weak derivatives,

$$
\begin{aligned}
(\overline L+1)(\zeta v)
={}&\zeta(E+gW+1)v
 -2\varepsilon^2\zeta_kv_k-\varepsilon^2\zeta_{kk}v\\
 &-\tfrac12\zeta_\alpha v_\alpha-\tfrac14\zeta_{\alpha\alpha}v.
\end{aligned}
\tag{4.4}
$$

Extend the compact height support by zero to $\mathbb R\times\mathbb T$.
The constant-coefficient operator on the left has Fourier symbol
$1+\varepsilon^2\xi^2+m^2/4$, so its inverse maps $H^s$ to
$H^{s+2}$. Starting from local $H^2$, the right side of (4.4) lies in
$H^1$ on compact supports. Thus $\zeta v\in H^3$. Using nested
cutoffs, local $H^m$ makes the right side $H^{m-1}$ and gives local
$H^{m+1}$ on a smaller neighborhood. Iteration gives every integer
Sobolev order; Fourier Cauchy--Schwarz then gives continuous derivatives
of every prescribed finite order. This proves smoothness away from
$x_o$. Smoothness at the base pole is not asserted. $\square$

**Theorem 4.2 (strict positivity, including at the base pole).** The
continuous representative in Theorem 4.1 satisfies

$$
v(k,\alpha)>0\qquad((k,\alpha)\in D).
\tag{4.5}
$$

This statement holds for positive, zero or negative $E$. On every compact
subset of $D$, $v$ has a strictly positive minimum. In particular $1/v$
is smooth with bounded derivatives on each compact subset away from
$x_o$.

Proof. Choose $s>\max\{0,-E\}$, so $E+s>0$. Equation (4.1) gives the
$L^2$ identity

$$
v=(\overline L+s)^{-1}\bigl[(E+s+gW)v\bigr].
\tag{4.6}
$$

The bracketed vector is nonnegative almost everywhere and is at least
$(E+s)v$. The free resolvent is positivity preserving because

$$
(\overline L+s)^{-1}F
  =\int_0^\infty e^{-st}e^{-t\overline L}F\,dt
\tag{4.7}
$$

as an $L^2$ integral, and the free heat kernel is positive. Positive
cones are closed in $L^2$, so truncation of this integral preserves its
order inequalities. Equations (4.6)--(4.7) imply almost everywhere

$$
v\ge\Psi,\qquad
\Psi(x)=(E+s)\int_1^2 e^{-st}
           \int_D\overline p_t(x,y)v(y)d\nu(y)dt.
\tag{4.8}
$$

For each interior $x$ and $1\le t\le2$ the kernel is strictly positive,
and $v\ge0$ has norm one. The inner integral is therefore strictly
positive. The base Fourier heat series and its derivatives converge
uniformly for these times when applied to an $L^2$ vector, so $\Psi$
is smooth and finite in the interior. Thus $\Psi(x)>0$ for every
$x\in D$.

The function $v-\Psi$ is continuous and is nonnegative almost everywhere.
If it were negative at an interior point it would be negative on an open
set of positive measure, a contradiction. Hence (4.8) holds at every
interior point, including $x_o$, and proves (4.5). This proof does not
evaluate the singular eigen-equation pointwise at $x_o$. Compactness
and continuity give the positive minimum assertion; away from $x_o$
Theorem 4.1 and differentiation of a reciprocal give the last assertion.
$\square$

## 5. The positive native harmonic and its explicit lower kernel

**Lemma 5.1 (inherited first harmonic with the original normalization).**
Define the unnormalized phase moment

$$
C_1(k)=\int_{\mathbb T^2}\Gamma_o(k,\alpha,\beta)
                      \cos(\beta-\beta_o)d\alpha d\beta.
\tag{5.1}
$$

This is an absolutely convergent integral at every $k\in I$. It equals
the Dirichlet Green kernel $R_1(k_o,k)$, relative to $dk$, for

$$
A_1=-\varepsilon^2\frac{d^2}{dk^2}+c(k)^2,
\qquad D(A_1)=H^2(I)\cap H^1_0(I).
\tag{5.2}
$$

For $a>0$ set

$$
R^{(a)}(k_o,k)=
\frac{
 \sinh\bigl(a(\min(k_o,k)-l)/\varepsilon\bigr)
 \sinh\bigl(a(u-\max(k_o,k))/\varepsilon\bigr)}
 {\varepsilon a\sinh(ad/\varepsilon)}.
\tag{5.3}
$$

Writing

$$
c_-=\tfrac12-u/r>0,\qquad c_+=\tfrac12-l/r>0,
\qquad R_+(k)=R^{(c_+)}(k_o,k),
\tag{5.4}
$$

the comparison is

$$
0<R_+(k)\le C_1(k)
 \le R^{(c_-)}(k_o,k)\le\varepsilon^{-2}G_I(k_o,k)
\qquad(k\in I).
\tag{5.5}
$$

Proof. This is [Q, Theorem 4.1]. Its correspondence and comparison are
included here because the mixed form below needs their exact factors.
Absolute convergence of (5.1) follows from (1.11) and $|\cos|\le1$.
The normalized angular character map

$$
\varphi(k)\longmapsto\frac{\varphi(k)}{2\pi}
 e^{i[m(\alpha-\alpha_o)+n(\beta-\beta_o)]}
\tag{5.6}
$$

is an isometry from $L^2(I)$ onto its angular sector. Directly on
smooth core functions it transforms the full free form into

$$
\int_I\left(\varepsilon^2|\varphi'|^2
                 +(m/2+nc(k))^2|\varphi|^2\right)dk.
\tag{5.7}
$$

The Fourier projection onto this sector is an average of phase
translations against a character. It preserves the smooth core and is
bounded in the free form norm, since these translations preserve $P,Q$
and $\mu$. Distinct sectors are form orthogonal. Closure therefore
makes (5.7) a reducing closed-form correspondence with height domain
$H^1_0(I)$. Its potential is smooth and bounded on the closed interval.
The one-dimensional weak equation then gives the operator domain
$H^2(I)\cap H^1_0(I)$, with the reverse inclusion by integration by
parts. For $m=0,n=\pm1$ the operator is (5.2).

In particular, for a compact smooth height test $a(k)$, evaluating the
free semigroup at the original point $o$ gives

$$
\left(e^{-tL}\bigl[a(k)\cos(\beta-\beta_o)\bigr]\right)(o)
       =(e^{-tA_1}a)(k_o).
\tag{5.8}
$$

The cosine has value one at the pole. Thus the phase integral of
$p_t^\Omega(o,(k,\alpha,\beta))\cos(\beta-\beta_o)$ equals the
one-dimensional heat kernel of $A_1$, first against height tests and
then pointwise by smoothness. There is no angular average in (5.8).
At each height the absolute integral of the full heat integrand over
time and phases is bounded by (1.11). Signed integration in time is
therefore legitimate and gives $C_1(k)=R_1(k_o,k)$, with no factor
$2\pi$ or $1/2$.

The positivity and comparison can also be seen directly at the resolvent
level. For any continuous $V\ge0$ on $[l,u]$, let $y$ solve
$-\varepsilon^2y''+Vy=0$ with $y(l)=0,y'(l)=1$, and let $z$ solve
the same equation with $z(u)=0,z'(u)=-1$. The equation
$y''=Vy/\varepsilon^2$ prevents a first positive-interval zero of $y$:
while $y>0$ its derivative cannot decrease below its initial positive
value. Reversing height gives the analogous assertion for $z$.
Consequently both are positive in the interior, and
$\mathcal W=y'z-yz'$ is a positive constant, equal to $z(l)>0$.
The Dirichlet Green kernel is

$$
R_V(a,k)=\frac{y(\min(a,k))z(\max(a,k))}
                     {\varepsilon^2\mathcal W}>0.
\tag{5.9}
$$

Its height derivative jump is $-1/\varepsilon^2$, so its source is a
unit delta relative to $dk$. If $0\le V_1\le V_2$, subtracting the
two inverse equations gives the resolvent identity

$$
R_{V_1}(a,k)-R_{V_2}(a,k)
 =\int_I R_{V_1}(a,s)(V_2(s)-V_1(s))R_{V_2}(s,k)ds\ge0.
\tag{5.10}
$$

All these regular one-dimensional kernels are continuous and bounded
on the closed interval. For $V=a^2>0$, formula (5.9) is precisely
(5.3); for $V=0$ it is $\varepsilon^{-2}G_I$.
Since $0<c_-\le c(k)\le c_+$ on $I$, apply (5.10) to
$0,c_-^2,c(k)^2,c_+^2$ in their indicated order. This proves (5.5).
In (5.3) both numerator factors and the denominator are strictly
positive for interior heights. $\square$

## 6. A compact reciprocal perturbation of the actual minimizer

**Definition 6.1 (remote compact perturbation).** Fix a nonnegative
normalized actual restricted minimizer $v$ as in Lemma 2.2, with its
representative from Theorems 4.1--4.2. Choose either component of
$I\setminus\{k_o\}$, an open interval $I_0$ compactly contained in
that component, and a real function

$$
0\ne\chi\in C_c^\infty(I_0),\qquad \chi\ge0.
\tag{6.1}
$$

Such a choice exists on either side of the interior source height.
On $I_0\times\mathbb T$ set $b=\chi/v$, and extend $b$ by zero to
the rest of $D$. Define

$$
f_0=Jv,\qquad
w(k,\alpha,\beta)=\frac{b(k,\alpha)}{\sqrt{2\pi}}
                      \cos(\beta-\beta_o),\qquad
N=\|w\|_2^2,\qquad K=T[w].
\tag{6.2}
$$

The reciprocal in this definition is taken only on the remote interior
strip. It is not an expression involving division at a height face or
at the base pole.

**Lemma 6.2 (actual core membership, norm and kinetic energy).** The
vector $f_0$ is a unit member of $\mathcal F$ with $q_g[f_0]=E$.
The vector $w$ is a nonzero member of the original core
$C_c^\infty(\Omega)$, with support separated from the source height.
Its norm and free energy are

$$
\begin{aligned}
0<N&=\frac12\int_D b^2d\nu<\infty,\\
K&=\frac12\int_D
  \left(\varepsilon^2b_k^2+\tfrac14b_\alpha^2+c(k)^2b^2\right)d\nu
  <\infty.
\end{aligned}
\tag{6.3}
$$

Moreover

$$
\Pi w=0,\qquad \langle f_0,w\rangle=0,\qquad
T(f_0,w)=0,
\tag{6.4}
$$

and both $q_g[w]$ and the mixed potential integral with $f_0$ are finite.

Proof. Equations (1.8), (1.15) and (2.5) give the assertions about
$f_0$. On the compact strip $\overline I_0\times\mathbb T$, the
minimizer is smooth and has a positive minimum by Theorems 4.1--4.2.
It is smooth on a neighborhood of this strip as well. Thus $\chi/v$
is smooth there. Since $\chi$ vanishes on neighborhoods of the two
endpoints of $I_0$, the zero extension of $b$ is smooth. Its support is
compact in height and every derivative is bounded on that support.
This proves $w\in C_c^\infty(\Omega)$ for exactly the core in (1.4).
It is nonzero because $\chi$ is nonzero and $v$ is finite and positive.

For $\vartheta=\beta-\beta_o$ the derivatives are

$$
Pw=\frac{b_k\cos\vartheta}{\sqrt{2\pi}},\qquad
Qw=\frac{\tfrac12b_\alpha\cos\vartheta-c(k)b\sin\vartheta}
          {\sqrt{2\pi}}.
\tag{6.5}
$$

The hidden integrals of $\cos^2\vartheta$ and $\sin^2\vartheta$ are
both $\pi$, and that of $\cos\vartheta\sin\vartheta$ is zero.
These identities give (6.3), including the original hidden kinetic term
$c(k)^2b^2$ and the base coefficient $1/4$.
The zero hidden mean gives $\Pi w=0$ and orthogonality to $f_0$.
The closed free form splitting (1.8) gives $T(f_0,w)=0$ on the actual
form domains. Finally the full field is smooth and bounded on the
compact support of $w$, while $f_0$ is continuous there. This proves
the asserted finiteness directly; (1.12) and weighted
Cauchy--Schwarz give it as well. $\square$

**Proposition 6.3 (exact native mixed form at the actual ground state).**
For the vectors of Definition 6.1,

$$
q_g(f_0,w)=-\frac{g}{2\pi}\int_I\chi(k)C_1(k)dk<0.
\tag{6.6}
$$

In particular the magnitude of this mixed form is at least

$$
\frac{g}{2\pi}\int_I\chi(k)R_+(k)dk>0.
\tag{6.7}
$$

Proof. The free mixed form vanishes by (6.4). On the support of $w$,
and with both sides zero outside its height support,

$$
f_0w=\frac{v(k,\alpha)b(k,\alpha)}{2\pi}
          \cos(\beta-\beta_o)
       =\frac{\chi(k)}{2\pi}\cos(\beta-\beta_o).
\tag{6.8}
$$

All functions in this pairing are real. Absolute integration on the
remote compact support and (5.1) give (6.6). The lower comparison
(5.5), $g>0$ and the nonzero nonnegative bump give (6.7).
This cancellation uses the actual, potentially $\alpha$-dependent,
minimizer. It does not require a sign for a ground-state-weighted
angular harmonic: after cancellation the harmonic is exactly $C_1$.
$\square$

## 7. Actual-minimum descent and two finite positive certificates

**Definition 7.1 (certificate data).** For any choices in Definition 6.1,
put $\eta=w/\sqrt N$ and define

$$
\begin{aligned}
A_\chi&=\frac{g}{2\pi\sqrt N}\int_I\chi(k)C_1(k)dk,
&a_\chi&=\frac{g}{2\pi\sqrt N}\int_I\chi(k)R_+(k)dk,\\
B_\chi&=\frac{q_g[w]}N-E,
&C_\chi&=\frac KN+gB_\varepsilon,\\
\Delta_\chi&=\frac{\sqrt{B_\chi^2+4A_\chi^2}-B_\chi}{2},
&\delta_\chi&=\frac{\sqrt{C_\chi^2+4a_\chi^2}-C_\chi}{2}.
\end{aligned}
\tag{7.1}
$$

The subscripts distinguish $B_\chi$ from the inherited nonnegative
constant $B_\varepsilon$. The values in (7.1) are real quantities
defined by the actual restricted minimizer, the chosen bump and the
one fixed native realization.

**Theorem 7.2 (strict actual fixed-pole ground-energy gap).** For every
choice of the original parameters in Definitions 1.1--1.4, under the
inherited analytic premises of Contract 1.3, every nonnegative normalized
restricted minimizer and every bump as in Definition 6.1 give

$$
E_{\rm base}-E_{\rm full}\ \ge\ \Delta_\chi
                 \ \ge\ \delta_\chi\ >\ 0.
\tag{7.2}
$$

Both energies are actual finite attained minima. More precisely, all
the certificate quantities are finite and satisfy

$$
A_\chi\ge a_\chi>0,\qquad
0\le C_\chi<\infty,\qquad B_\chi\le C_\chi,
\tag{7.3}
$$

with no sign restriction on $B_\chi$ or $E$. The number
$E-\Delta_\chi$ is the exact minimum of the form on the unit sphere
of $\operatorname{span}\{f_0,\eta\}$. An explicit unit form vector is

$$
\begin{gathered}
\delta_\chi=
 \frac{2a_\chi^2}{\sqrt{C_\chi^2+4a_\chi^2}+C_\chi},\qquad
t_\chi=\frac{\delta_\chi}{a_\chi}>0,\\
f_\chi=\frac{f_0+t_\chi\eta}{\sqrt{1+t_\chi^2}}
       \in\mathcal F,\qquad
\|f_\chi\|_2=1,\qquad q_g[f_\chi]\le E-\delta_\chi.
\end{gathered}
\tag{7.4}
$$

Neither $\Delta_\chi$ nor $\delta_\chi$ is asserted to equal the full
energy difference. No negative-binding hypothesis is needed.

Proof. Theorem 2.1 gives both finite attained minima. Lemma 6.2 gives
$N>0$, finite $K$, and the orthonormal form vectors $f_0,\eta$.
The integrals in (7.1) have compact height support; Lemma 5.1 and
Proposition 6.3 give their finiteness and $A_\chi\ge a_\chi>0$.
Positivity of the original full field implies $q_g[w]\le K$, while
(2.1) gives $E\ge-gB_\varepsilon$. Therefore

$$
B_\chi=\frac{q_g[w]}N-E
       \le\frac KN+gB_\varepsilon=C_\chi,
\qquad C_\chi\ge0.
\tag{7.5}
$$

The number $B_\chi$ can have either sign. All denominators $N$,
$\sqrt N$ and $2\pi\sqrt N$ are positive.
The symmetric matrix of the form on these two orthonormal vectors is

$$
\begin{pmatrix}
E&-A_\chi\\
-A_\chi&E+B_\chi
\end{pmatrix}.
\tag{7.6}
$$

This is a restriction of a form to a finite-dimensional subspace.
In particular it is not an assertion that either vector belongs to the
full attractive operator domain. For every real $t$ its normalized
Rayleigh value is exactly

$$
q_g\left[\frac{f_0+t\eta}{\sqrt{1+t^2}}\right]
 =E+\frac{B_\chi t^2-2A_\chi t}{1+t^2}.
\tag{7.7}
$$

The characteristic equation of (7.6), after subtracting $E$, is
$\lambda^2-B_\chi\lambda-A_\chi^2=0$. Its lower root is
$-\Delta_\chi$. Since $A_\chi>0$, one has
$\sqrt{B_\chi^2+4A_\chi^2}>|B_\chi|$, so
$0<\Delta_\chi<\infty$ even when $B_\chi<0$.
Equivalently

$$
\Delta_\chi(\Delta_\chi+B_\chi)=A_\chi^2,
\qquad
\Delta_\chi=
 \frac{2A_\chi^2}{\sqrt{B_\chi^2+4A_\chi^2}+B_\chi},
\tag{7.8}
$$

where the denominator is strictly positive. The lower eigenvector may
be taken proportional to $(1,\Delta_\chi/A_\chi)$.
Thus the exact two-dimensional minimum is $E-\Delta_\chi$, and
inclusion of this form subspace in $\mathcal F$ proves
$E-E_{\rm full}\ge\Delta_\chi$.

Likewise $a_\chi>0$ and $C_\chi\ge0$ show that $\delta_\chi$ is
finite and strictly positive, with the positive denominator in (7.4).
It is the positive root of

$$
\delta_\chi^2+C_\chi\delta_\chi=a_\chi^2.
\tag{7.9}
$$

Using (7.3) and (7.9),

$$
\delta_\chi^2+B_\chi\delta_\chi-A_\chi^2
 =(B_\chi-C_\chi)\delta_\chi+(a_\chi^2-A_\chi^2)\le0.
\tag{7.10}
$$

The polynomial on the left, as a function of its nonnegative argument,
has its unique positive zero at $\Delta_\chi$ and its other zero
strictly negative. Hence $\delta_\chi\le\Delta_\chi$, proving the
second inequality in (7.2) without a sign assumption on $B_\chi$.

For the explicit vector in (7.4), both form membership and normalization
follow from Lemma 6.2. Since $t_\chi>0$, (7.3) and (7.7) give

$$
q_g[f_\chi]-E
 \le\frac{C_\chi t_\chi^2-2a_\chi t_\chi}{1+t_\chi^2}
 =-\delta_\chi.
\tag{7.11}
$$

For the last equality substitute $t_\chi=\delta_\chi/a_\chi$ and
$a_\chi^2=\delta_\chi^2+C_\chi\delta_\chi$ into both numerator
and denominator. Its denominator is $1+t_\chi^2>0$.
This independently exhibits a unit admissible full vector with energy
strictly below the actual restricted minimum, not merely below a
restricted trial value. All sign and domain arguments use only strict
stability, never $E<0$. $\square$

## 8. Endpoints, domain boundaries and the meaning of the certificate

**Proposition 8.1 (equality at zero coupling).** For the same fixed
positive $\varepsilon$ and native free domains, at $g=0$ one has

$$
E_{\rm full}(0)=E_{\rm base}(0)=\frac{\varepsilon^2\pi^2}{d^2}.
\tag{8.1}
$$

Proof. Height Poincare on each phase fiber gives on the full smooth core

$$
T[f]\ge\varepsilon^2\|Pf\|_2^2
       \ge\frac{\varepsilon^2\pi^2}{d^2}\|f\|_2^2.
\tag{8.2}
$$

This extends to $\mathcal F$ by its defining closure. The same bound
holds for $\overline T$. With
$\phi_1(k)=\sqrt{2/d}\sin(\pi(k-l)/d)$, the normalized vectors
$\phi_1/(2\pi)$ on $\Omega$ and $\phi_1/\sqrt{2\pi}$ on $D$
have no angular energy and attain (8.2). They belong to the declared
form domains by the one-dimensional Dirichlet approximation.
This proves (8.1). At this endpoint $a_\chi=0$, so the definition of
$t_\chi$ in (7.4) is not used. $\square$

**Boundary 8.2 (parameter, domain and interpretation limits).** Theorem
7.2 has the following precise scope.

- It holds for each fixed $\varepsilon>0$ and every $g=\gamma\varepsilon^2$
  in the original strict range $0<\gamma<(2rC_H)^{-1}$. The source's
  separate sufficient negative-binding condition is

  $$
  \varepsilon^2<\frac{\gamma M_od^2}{4\pi^4},\qquad
  M_o=\int_I G_I(k_o,k)|\phi_1(k)|^2dk>0,
  \tag{8.3}
  $$

  as in [Q, Corollary 7.2]. Condition (8.3) is not required anywhere
  above. In particular the theorem covers positive, zero and negative
  restricted ground energy.
- Critical equality $\gamma=(2rC_H)^{-1}$ is excluded: (2.3) then
  loses the positive coefficient of the free kinetic form. The argument
  proves neither a critical realization nor a sharp stability threshold.
  The constant $C_H$ retains its sufficient source meaning.
- The contract excludes $\varepsilon=0$, $Z=0$ or $1$, a collapsed
  interval, a pole on a height face and loss of $I\Subset(0,h)$.
  No limiting operator or conclusion at any of these endpoints is
  supplied. Both remote sides of the source height are nonempty under
  the stated assumptions.
- Ground-state degeneracy is allowed. The proof uses the modulus of
  any normalized restricted minimizer and does not assume simplicity of
  either ground eigenspace. Every such choice gives its own certificate.
- The base minimizer has zero values at the height faces. Its reciprocal
  is used only on the proved positive remote strip. Positivity at $x_o$
  is established by Theorem 4.2, but no reciprocal perturbation or
  differentiability assertion is used at that singular point.
- The lifted minimizer $f_0$ is used in the full form domain only.
  Neither $f_0\in D(H_g)$ for the full attractive form operator nor
  $\Gamma_of_0\in L^2(\Omega)$ is needed or asserted. The proved
  base membership $v\in D(\overline L)$ is a different statement.
  In particular no singular unbounded operator is multiplied in blocks.
- The full field remains (1.7) at the same point $o$, with the same
  Haar measures, boundaries and clock. The comparison is not between
  different poles, and no smeared, finite-time, Euclidean or Hardy
  replacement field enters either full energy or the mixed form.
- The lower certificate depends on the fixed parameters, the actual
  normalized $v$, the bump $\chi$, and the inherited finite
  $B_\varepsilon$. The reciprocal norms and derivatives in $N,K$ are
  part of this dependence. It is a finite positive mathematical
  certificate, not an evaluated number or a parameter-only closed
  formula. The exact-span value $\Delta_\chi$ and the sufficient value
  $\delta_\chi$ need not be the full gap or optimal over perturbations.
  No uniform lower bound as $g\downarrow0$, $\varepsilon\downarrow0$,
  the pole approaches a face, or other parameters vary is proved.
- These conclusions concern the specified Hilbert-space forms. They
  supply no physical amplitude-preparation or measurement procedure,
  finite-bit acquisition guarantee, empirical learning claim or
  conclusion about the original hidden-dimension problem.

## 9. Result map, source credit and mathematical contribution

The numbering separates inherited analytic data from the additional
ground-state argument. The full map is:

| Item | Result or role | Dependencies and scope |
| --- | --- | --- |
| Definition 1.1 | Native parameters, torus coordinates, measures, fields and clock | [Q, Definitions 1.1--1.3]; unchanged point-source realization |
| Definition 1.2 | Original full horizontal domain, base domain, isometry and form-operator convention | [Q, Definition 1.3 and Theorem 2.1] |
| Contract 1.3 | Explicit inherited kernel, free-domain, heat-marginal and full form-bound premises | The only source-specific analytic premises imported from [Q] |
| Definition 1.4 | Strict coupling, same-field restriction and the two actual infima | Contract 1.3 and the unnormalized hidden-circle factor |
| Theorem 2.1 | Closedness, strict shifted coercivity and finite actual attainment on both domains | Full bound and compact free embedding; no binding condition |
| Lemma 2.2 | Actual nonnegative base minimizer and weak eigen-equation | Modulus inequality and variational minimality |
| Lemma 3.1 | Logarithmic base Green upper bound, every finite $L^p$, smoothness off the base pole | Original heat product and off-pole full smoothness |
| Lemma 3.2 | Base $H^1$ to $L^4$ estimate | Odd extension and Fourier inequalities in two dimensions |
| Theorem 4.1 | $Wv\in L^2$, actual free base operator-domain membership, $H^2$, continuity and local smoothness | Lemmas 2.2, 3.1--3.2 and the exact base operator domain |
| Theorem 4.2 | Strict positivity at every interior base point, including the pole | Theorem 4.1 and a shifted positive free resolvent; arbitrary sign of $E$ |
| Lemma 5.1 | Native harmonic $C_1=R_1>0$ and explicit $R_+$ lower comparison | Inherited [Q, Theorem 4.1], with its normalization and comparison displayed |
| Definition 6.1 | Remote compact reciprocal perturbation of an actual minimizer | Theorems 4.1--4.2 and an interior bump |
| Lemma 6.2 | Actual smooth-core membership, finite positive norm, exact original kinetic energy and orthogonality | Remote support and the closed free form splitting |
| Proposition 6.3 | Strictly negative mixed form with exact factor $g/(2\pi)$ | Reciprocal cancellation and the native harmonic |
| Definition 7.1 | Finite certificate data $A_\chi,a_\chi,B_\chi,C_\chi,\Delta_\chi,\delta_\chi$ | The actual base minimizer, original field and explicit lower kernel |
| Theorem 7.2 | $E_{\rm base}-E_{\rm full}\ge\Delta_\chi\ge\delta_\chi>0$ and an explicit unit form trial | Actual attainment, admissible mixed form and two-dimensional Rayleigh algebra |
| Proposition 8.1 | Equal free minima at $g=0$ | Height Poincare and the angularly constant first sine mode |
| Boundary 8.2 | Endpoint, domain, parameter-dependence and interpretation limits | No extension of Theorem 7.2 beyond its displayed contract |

The necessary mathematical source credit is as follows. Content hashes
identify the supplied texts; they do not certify their mathematical truth.

| Source | Precise mathematical use |
| --- | --- |
| [Q] *Native observation quotient, hidden Green harmonics and attractive response*, SHA-256 `97d5082350d496499ec28ee44770212d2075570d78d0026610b65f71040179fa` | Native realization, explicit inherited analytic contract and the positive first harmonic. Definitions 1.3 and 3.2 there attribute the full heat and form-bound inputs to their analytic suppliers. Those statements, as reproduced in Contract 1.3, are the premises here. |
| [C] Supplied mathematical note, *Strict native fixed-pole ground-energy descent throughout the original strict stable regime*, SHA-256 `899c6d4f3f6a71d605f3de9deea84bbe0f949ad7e3aab9fc965833c33097b61f` | Credit for the compact reciprocal-ground-state construction and the two positive certificates. Their complete derivation is in Sections 2--7 of this volume. |
| [R] Supplied mathematical note, *The actual full minimum is strictly below the actual restricted minimum throughout the sealed strict stable regime*, SHA-256 `d3acfdc6a69b0553ebaadeea41d0f0c2fe0067fa185149735645d790587e001d` | Credit for the detailed coercivity, Fourier-domain, positivity and certificate-sign clarifications embodied in the proofs above. No assessment or endorsement in that note is a mathematical premise. |

The full singular heat-kernel and form-bound facts of Contract 1.3 remain
inherited handwritten premises; their nested suppliers are not independently
established here. The base logarithmic estimate, actual-minimizer
regularity and positivity, remote reciprocal admissibility and mixed-form
calculation are proved in this volume from those premises. Source-specific
contributions are the connection of those bridges to the native positive
harmonic and the resulting strict comparison of the two actual minima
throughout the original strict stable range.

The two-vector Rayleigh calculation, Fourier Sobolev estimates,
positive-resolvent argument and one-dimensional Green comparison are
standard mathematical methods. They are not claimed as new general
theorems. The source-specific synthesis is `repo-derived`; no worldwide
originality claim or independent external-literature verification is made.
The trial-energy separation and projected-response defect in [Q,
Theorems 5.2 and 6.1] remain distinct results. They supply neither the
actual minimizer nor a substitute for the admissible descent proved here.

## 追加锚（本行以下为增补区）
