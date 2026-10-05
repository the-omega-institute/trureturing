# Regulated complete-prime costs on a common source

Use the [original weighted high comparison](../../../Library/Weil/fukushima2011dirichlet.md#spatially-weighted-high-inverse-at-every-subcritical-parameter)
and [common-source constrained inverse](sharp-center.md#pay-weighted-action-errors-with-one-common-dual-source)
on the unchanged even minimal realization. The
[critical-zero range obstruction](critical-prime-source-range.md) excludes
a blanket exact endpoint factorization. A positive exterior reserve
instead permits the quantitative full-prime budget below.

This is a conditional paper application of inherited original-model and
published counting premises. It gives no numerical result, low-block
sign, all-input half-bound, full Robin, RH, generic theorem, priority
or Lean certificate.

## A complete count controls the positive-reserve budget

The existing [Johnston--Yang all-prime-power estimate](../../../Library/Weil/johnstonyang2022pnt.md)
and [half-weight partial summation](../../../Library/Weil/chirrehelfgott2025nonnegative.md#a-complete-lower-interval-budget-from-the-same-source)
already supply the counting input needed here. Reuse them without new
prime enumeration, zero verification or source acquisition. The relative
Johnston--Yang envelope has a finite supremum; for example the fixed
constant

$$
C_\Psi=1+9.39\left(\frac{3.03}{0.8274e}\right)^{3.03}
$$

gives $\Psi(X)\le C_\Psi X$ for $X\ge1$. The interval $1\le X<2$
has no Mangoldt atoms. The existing partial summation then gives

$$
A_{1/2}(X)=\sum_{n\le X}\frac{\Lambda(n)}{\sqrt n}
\le 2C_\Psi\sqrt X,\qquad X\ge1.
$$

These are applications of the pinned complete cumulative bound, not a
new PNT or signed discrepancy estimate. Keep the [original theta envelope](vanishing-exterior-reserve.md)'s
$s(x)\le K\exp(-b e^{2|x|})$, and write $s_*=\|s\|_\infty$.
For any bounded even $u$, set $h=su$ and retain the complete action

$$
\mathcal P h(x)=\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}
[h(x-\log n)+h(x+\log n)].
$$
Define the finite positive constant

$$
C_{\rm p}=4C_\Psi\sqrt e\left[
s_*+K\sqrt2\sum_{k\ge0}2^{k/2}e^{-b e^2 4^k}\right].
$$

Then

$$
|\mathcal P(su)(x)|
\le C_{\rm p}\|u\|_\infty e^{|x|/2}. \tag{RP1}
$$

For $x\ge0$, split at $X=e^{x+1}$. The initial complete half-weight
is at most $2C_\Psi\sqrt X$; each of its two responses is at most
$s_*\|u\|_\infty$. In the block $2^kX<n\le2^{k+1}X$, both theta
factors are at most $K e^{-b e^2 4^k}$, and the full half-weight is
at most $2C_\Psi\sqrt{2^{k+1}X}$. Sum these nonnegative bounds.
Evenness covers the other half-line. The same majorants prove absolute
convergence. Both shifted responses and every prime power are retained.

For $a,\delta>0$ set

$$
\begin{aligned}
A&=\frac{aK^2}{\delta},& \kappa&=2b,&
T&=\max\{1,\kappa^{-1}\log A\},\\
\mathcal L(A)&=2(\sqrt T-1)+\frac1{\kappa\sqrt T}.
\end{aligned}
$$

The complete prime action satisfies the regulated allowance

$$
\int_{\mathbb R}
\frac{|s\mathcal P(su)|^2}{\delta+a s^2}\,dx
\le\frac{C_{\rm p}^2}{a}\mathcal L(A)\|u\|_\infty^2.
\tag{RP2}
$$

Indeed

$$
\frac{s^2}{\delta+a s^2}
\le\frac1a\min\{1,Ae^{-\kappa e^{2|x|}}\}.
$$

After squaring (RP1), substitution $t=e^{2|x|}$ on both half-lines
leaves

$$
\int_1^\infty t^{-1/2}\min\{1,Ae^{-\kappa t}\}\,dt.
$$

The segment $[1,T]$ contributes at most $2(\sqrt T-1)$. Since
$Ae^{-\kappa T}\le1$, the remaining segment is at most
$T^{-1/2}\int_0^\infty e^{-\kappa v}dv$. This also covers
$A\le e^\kappa$, when $T=1$. No lower envelope for $s$ is assumed.
For fixed $a$, the resulting upper allowance grows at most as
$\sqrt{\log(1/\delta)}$. It keeps $\delta>0$ and is compatible with
the endpoint range obstruction; it does not give an exact endpoint
factorization or a lower bound on the actual inverse cost.

## Use one centered source in the constrained inverse

Use exactly (WH1)'s $\varepsilon,c,\delta,N,a_N$, original high
operator $C$ and unit ground $v_0$. Take $u$ in the original even
$H^2$ operator-domain class used for the high trials. Full-ground-center
the same source:

$$
\bar u=u-\langle u,v_0\rangle v_0,\qquad
T_c\bar u=T_cu,\qquad r=QT_cu.
$$

This map is linear under the first-slot-linear convention. It does not
change the high residual. The original centered action gives

$$
\begin{aligned}
T_c\bar u&=\varepsilon\bar u+
s[g_{\bar u}-\mathcal P(s\bar u)],\\
g_{\bar u}&=m(\mathsf D)(s\bar u)+c_\Gamma s\bar u\in L^2.
\end{aligned}
\tag{RP3}
$$

The inherited bounded theta derivatives and logarithmic symbol estimate
give the stated $L^2$ membership. Choose the actual low dual lift
$h_{\rm low}=PT_cu$. Reuse (SC19) with
$F=M_{\delta+a_Ns^2}+c|v_0\rangle\langle v_0|$ and
$0\preceq F^{-1}\preceq M_w$; the three-term squared-norm bound yields

$$
\begin{aligned}
\langle r,C^{-1}r\rangle
&\le J(r)\le\langle T_c\bar u,F^{-1}T_c\bar u\rangle\\
&\le3\left[
\frac{\varepsilon^2}{\delta}\|\bar u\|_2^2+
\frac{\|g_{\bar u}\|_2^2}{a_N}+
\frac{C_{\rm p}^2}{a_N}
\mathcal L\!\left(\frac{a_NK^2}{\delta}\right)
\|\bar u\|_\infty^2\right].
\end{aligned}
\tag{RP4}
$$

The inverse retains the exact rank-one ground. Dropping its nonnegative
inverse saving enlarges this explicit allowance. No new shorting theorem
or endpoint high comparison is introduced.

For one finite common linear source $u(z)$, let $G_0,G_g$ be its actual
centered Hermitian Grams for $\|\bar u(z)\|_2^2$ and
$\|g_{\bar u(z)}\|_2^2$. Choose a simultaneous positive Hermitian
upper Gram $G_\infty$ for $\|\bar u(z)\|_\infty^2$, with
$G_\infty e_0=0$ when $u_0=v_0$. This ground-null requirement is part
of the certificate; it does not follow for an arbitrary upper Gram.
For a fixed family of $d$ columns, the valid choice
$d\,\operatorname{diag}(\|\bar u_i\|_\infty^2)$ follows from
Cauchy--Schwarz and has this exact ground-nullity. Its dimension factor
must remain in a growing-family budget. The same coefficients give

$$
\langle r(z),C^{-1}r(z)\rangle
\le3z^*\left[
4\varepsilon G_0+\frac{G_g}{a_N}+
\frac{C_{\rm p}^2}{a_N}
\mathcal L\!\left(\frac{a_NK^2}{\delta}\right)G_\infty
\right]z. \tag{RP5}
$$

When $u_0=v_0$, centering makes all these residual source Grams have
exactly zero ground row and column. The nonzero ground trial contribution
from (SC14) remains; only the residual-cost allowance vanishes there.

## The cofinal rate still requires the actual common Grams

The first (WH1) cutoff gives
$\mu_\varepsilon\le\frac14\log(N/2)-1$. Combine it with (WF3)'s
$m(N/2)\ge\frac12\log(N/2)-1$ to obtain

$$
a_N\ge\frac14\log(N/2). \tag{RP6}
$$

This uses no boundedness assumption on $\mu_\varepsilon$. The other
(WH1) cutoff, with the nonzero original $\|s''\|_2$, implies
$a_N\ge\frac18\log(1/\varepsilon)+O(1)$. Consequently along every
(WH1) sequence $\varepsilon\downarrow0$,

$$
\frac1{a_N}\longrightarrow0,\qquad
\frac{\mathcal L(a_NK^2/\delta)}{a_N}\longrightarrow0.
\tag{RP7}
$$

For the second limit use
$\mathcal L(A)=O(1+\sqrt{\log_+A})$ and
$\log A=\log(1/\varepsilon)+\log a_N+O(1)$.
Both $\sqrt{\log(1/\varepsilon)}/a_N$ and
$\sqrt{\log_+a_N}/a_N$ tend to zero. Faster bandwidth growth does
not invalidate this scalar limit.

For an actual changing coefficient family, the explicit upper allowance
in (RP5) tends to zero if its common Grams satisfy

$$
\varepsilon\|G_0\|\to0,\qquad
\frac{\|G_g\|}{a_N}\to0,\qquad
\frac{\mathcal L(a_NK^2/\delta)}{a_N}\|G_\infty\|\to0.
\tag{RP8}
$$

Uniformly bounded common Grams suffice. A growing low unit sphere can
instead have $\|p\|_\infty^2$ of order $N$; increasing the band alone
does not establish (RP8).

For a fixed finite original $H^2$ family $u_i$, including the true ground,
choose $p_{i,N}=P_Nu_i$ and $q_{i,N}=-Q_Nu_i$. These are legitimate
original low inputs and regular high trials, and their residual is
$Q_NT_cu_i$. The centered sources and common Grams are fixed, so (RP5)'s
residual allowance tends to zero on that one (WH1) sequence. This is a
quantitative complete-prime source budget for the fixed family.
The existing (FF) result already supplies finite approximation; no
additional rank theorem, finite numerical benchmark or algorithmic
improvement is claimed.

Using this allowance for a growing all-input family requires establishing
(RP8) together with its actual low and complementary-low signs on the same
sequence. These are sufficient budget conditions, not necessary conditions
for convergence of the actual inverse cost or for RH. Neither sign follows
from this budget. The original all-input half-bound,
full Robin, RH, numerical enclosure and Lean certification remain unresolved.

## Choose one schedule for prescribed growing sources

The existence of a cofinal schedule for prescribed finite sources
already follows from the existing scalar (WH4) floor and strong sharp
Fourier-tail convergence. Reuse that existence result. The construction
below only makes (RP5)'s complete-prime source-norm conditions explicit;
it supplies no additional existence or finite-approximation theorem.


The uniform-Gram condition is sufficient but need not be imposed on
every growing family. Let $\mathcal U_j$ be a prescribed finite original
$H^2$ source family, including the true ground. Its columns and common
Grams are fixed before selecting the new $\varepsilon_j,N_j$.
Let $\tau_j>0$ tend to zero, set $N_0=0$, and write

$$
M_{0,j}=\|G_{0,j}\|,\qquad
M_{g,j}=\|G_{g,j}\|,\qquad
M_{\infty,j}=\|G_{\infty,j}\|.
$$

These finite norms may grow. Choose a single decreasing sequence with

$$
0<\varepsilon_j\le
\min\left\{\frac14,\frac{\varepsilon_{j-1}}2,
\frac{\tau_j}{36\max\{1,M_{0,j}\}}\right\},
\qquad \delta_j=\varepsilon_j/4,
\tag{RP9}
$$

where the previous-parameter constraint is omitted at the first index.
At this already chosen parameter select one
$N_j\ge\max\{N_w(\varepsilon_j),N_{j-1}+1,j\}$ so large that its
actual $a_j=m(N_j/2)-\mu_{\varepsilon_j}$ satisfies

$$
\frac{M_{g,j}}{a_j}\le\frac{\tau_j}{9},\qquad
\frac{C_{\rm p}^2M_{\infty,j}}{a_j}
\mathcal L\!\left(\frac{a_jK^2}{\delta_j}\right)
\le\frac{\tau_j}{9}. \tag{RP10}
$$

For each fixed $\varepsilon_j$, $\mu_{\varepsilon_j}$ is finite
and $a_N\to\infty$ as $N\to\infty$. The scalar function
$\mathcal L(aK^2/\delta_j)/a$ tends to zero. Thus both conditions
can be met by the same finite $N_j$, with the original (WH1) high
comparison intact. No bounded-$\mu$ assumption or independent best
choices of sources, parameter and band are combined.

With the actual $p_{i,j}=P_{N_j}u_{i,j}$,
$q_{i,j}=-Q_{N_j}u_{i,j}$ and the same coefficient vector, (RP5) gives

$$
\langle r_j(z),C_j^{-1}r_j(z)\rangle
\le J_j(r_j(z))\le\tau_j\|z\|^2.
\tag{RP11}
$$

Indeed each of (RP5)'s three nonnegative terms is at most
$\tau_j\|z\|^2/3$. This organizes the actual complete-prime residual
budget on one common cofinal sequence for the prescribed source
families; it is an application of the existing parameter limits,
not a new generic diagonal or finite-approximation theorem.

The construction gives existence and an explicit inequality interface
in the actual source norms, without certified numerical values or a
runtime bound. If a family instead depends on the newly selected band,
its changing norms must still be controlled jointly; (RP9)--(RP10)
cannot treat them as constants selected beforehand. The entire
complementary-low space has not been covered. Actual low and
complementary-low signs on this sequence, the original all-input
half-bound, full Robin and RH remain unproved.


## Center before paying the complete-prime discrepancy

The [centered discrepancy budget](centered-prime-discrepancy-budget.md)
reuses the same complete Chebyshev error on exactly full-ground-centered
even $H^2$ sources. It cancels their continuous main term while retaining
the $t=0$ endpoint, both shifts and every prime power. Paying
$D(u)=\|u\|_\infty+\|u'\|_\infty$ gives a regulated prime allowance
with $\mathcal J(T)=o(\sqrt T)$ for a fixed centered source. The
archimedean/scalar costs and SC14's separate ground trial term remain.
Changing families still need common derivative/source Grams; no uniform
gain, numerical saving, actual inverse convergence or cofinal sign is
asserted.


## The regulator also pays an L2 source norm

Retain the same positive $a,\delta$, theta envelope, complete
$\mathcal P$ and (RP1) constants. The
[existing Schur supplier](../../../Library/Fourier/teschl2009mathematical.md#schur-criterion-for-the-local-frequency-kernel)
provides the classical row/column estimate. Applied to the actual
regulated translation weights, it gives an $L^2$ source budget; no
new generic Schur, counting or cofinal-existence theorem is needed.
This is a conditional paper/model application, without numerical,
priority or Lean claims.

Put

$$
r(x)=\frac{s(x)}{\sqrt{\delta+a s(x)^2}},\quad
A=\frac{aK^2}{\delta},\quad T=\max\{1,\log A/(2b)\},\quad
L=\tfrac12\log T.
$$

Then $r(x)\le a^{-1/2}\min\{1,\sqrt A e^{-b e^{2|x|}}\}$
and $\sqrt A e^{-bT}\le1$. Define the fixed finite constants

$$
\begin{aligned}
c_b&=(4be)^{-1/4},& S_s&=\sup_x s(x)e^{|x|/2},\\
C_r&=4C_\Psi\sqrt e\left[1+\sqrt2
\sum_{k\ge0}2^{k/2}e^{-b(e^2 4^k-1)}\right],\\
C_2&=C_{\rm p}(1+c_b)S_sC_r.
\end{aligned}
$$

The theta envelope makes $S_s$ finite. The constants do not depend
on the source, regulator or bandwidth. Both shifts and every prime
power remain in the nonnegative weights of
$\mathcal A_{a,\delta}u=r\mathcal P(su)$.

The row sum is $R(x)=r(x)\mathcal Ps(x)$. Reuse (RP1) at $u=1$.
For $t=e^{2|x|}$,

$$
R(x)\le\frac{C_{\rm p}}{\sqrt a}t^{1/4}
\min\{1,\sqrt A e^{-bt}\}
\le\frac{C_{\rm p}(1+c_b)}{\sqrt a}T^{1/4}.
\tag{RS1}
$$

For $t\le T$ use $t^{1/4}\le T^{1/4}$. For $t=T+v\ge T$,
use $\sqrt A e^{-bt}\le e^{-bv}$,
$(T+v)^{1/4}\le T^{1/4}+v^{1/4}$ and
$v^{1/4}e^{-bv}\le c_b$. Since $T\ge1$, this includes $T=1$.

The column sum of the same operator, including both shifted adjoints,
is $C(y)=s(y)\mathcal Pr(y)$. Split the complete count at
$X=e^{|y|+L+1}$. Each initial response is at most $1/\sqrt a$.
In $2^kX<n\le2^{k+1}X$, both arguments satisfy
$|y\pm\log n|\ge L+1+k\log2$, so

$$
r(y\pm\log n)\le\frac1{\sqrt a}\sqrt A e^{-bT e^2 4^k}
\le\frac1{\sqrt a}e^{-bT(e^2 4^k-1)}
\le\frac1{\sqrt a}e^{-b(e^2 4^k-1)}.
$$

The inherited complete half-weight count and (RP1)'s dyadic grouping give

$$
\mathcal Pr(y)\le\frac{C_r}{\sqrt a}e^{|y|/2}T^{1/4},\qquad
C(y)\le\frac{S_sC_r}{\sqrt a}T^{1/4}.
\tag{RS2}
$$

Cauchy--Schwarz on finite translation sums, followed by the same change
of variables in both shifted terms, gives
$\int|\mathcal A_{a,\delta}u|^2\le(\sup R)\int C(y)|u(y)|^2dy$.
Tonelli and these finite majorants supply the bounded extension and
absolute convergence almost everywhere on all complex $L^2$ sources.
Consequently,

$$
\int_{\mathbb R}\frac{|s\mathcal P(su)|^2}{\delta+a s^2}dx
\le\frac{C_2\sqrt T}{a}\|u\|_2^2.
\tag{RS3}
$$

This budget needs neither a source derivative nor a source supremum.
Evenness is unnecessary for (RS3); the original even $H^2$ source
domain remains in its operator application. It supplies no unweighted
$\mathcal P(su)\in L^2$ statement or zero-reserve factorization.

Use (RP4)'s same WH1 parameter, original unit ground, exact
$\bar u=u-\langle u,v_0\rangle v_0$, low dual lift and
$\rho=QT_cu=QT_c\bar u$. Replace only its prime source term:

$$
\langle\rho,C^{-1}\rho\rangle\le
3\left[4\varepsilon\|\bar u\|_2^2
+\frac{\|g_{\bar u}\|_2^2}{a_N}
+\frac{C_2\sqrt{T_N}}{a_N}\|\bar u\|_2^2\right],\qquad
T_N=\max\{1,\log(a_NK^2/\delta)/(2b)\}.
\tag{RS4}
$$

For a common family, use its actual $G_0$ with
$z^*G_0z=\|\sum z_i\bar u_i\|_2^2$. The exact ground is in its
kernel, with no dimension factor or separately optimized columns.
All scalar and archimedean terms and SC14's separate ground trial
contribution $C[q_0]$ remain. Only residual source costs vanish on
the ground column.

(RP7) already gives $\sqrt{T_N}/a_N\to0$ on every WH1 cofinal
sequence. Thus this **prime-source allowance** vanishes uniformly on
normalized original sources, including the exactly centered sharp-low
unit ball with $q=0$, whose centered norm is at most one.
The entire residual allowance has not been shown to vanish uniformly:
the actual archimedean Gram remains payable, and high lifts must pay
their actual $G_0$ growth. Sufficient conditions for this explicit residual upper allowance
to vanish are $\varepsilon\|G_0\|\to0$, $\|G_g\|/a_N\to0$ and
$(\sqrt{T_N}/a_N)\|G_0\|\to0$. They are not asserted necessary
for actual inverse convergence or the RH/Robin targets.

The [derivative-centered budget](centered-prime-discrepancy-budget.md)
remains separately available with its derivative expense. (RS3) has
not been shown numerically smaller. Actual inverse convergence,
complementary-low coverage, same-sequence signs, the original all-input
half-bound, full Robin, RH and Lean certification remain unresolved.
