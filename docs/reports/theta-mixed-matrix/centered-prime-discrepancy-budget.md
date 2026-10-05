# Center the same source before paying complete-prime discrepancy

The [regulated source budget](regulated-prime-source-budget.md) uses the
complete cumulative count at a positive exterior reserve. For a smooth
source with exact full-ground centering, the same complete
[Johnston--Yang error estimate](../../../Library/Weil/johnstonyang2022pnt.md)
can be used after its continuous main term cancels. The extra source
**derivative norm is paid** in the resulting allowance.

This is a conditional paper/model application of pinned theta,
original-domain and arithmetic premises. It gives no new PNT,
Stieltjes or cofinal-existence theorem, numerical saving, priority
claim, Lean certificate, low-block sign, all-input half-bound or RH.

## Retain the endpoint and cancel only the actual common main term

Use the original even theta weight $s$ and an even $H^2$ source $u$ with
$\langle u,v_0\rangle=0$, where $v_0=2s\cosh(x/2)$ is the inherited
unit ground, $\|v_0\|_2=1$. Use the
[first-slot-linear pairing](README.md#complex-inner-products-for-matrix-reports)
and set $h=su$.
Evenness and that exact constraint give

$$
\int h(y)e^{-y/2}dy=\int h(y)e^{y/2}dy=0.
$$

The [existing derivative envelopes](../../../Library/Analytic/romik2021orthogonal.md#weighted-fourier-coefficient-suppliers)
(WC2) supply common $K_0,K_1,b>0$ with
$|s^{(j)}(x)|\le K_j e^{-b e^{2|x|}}$, $j=0,1$. Put

$$
D(u)=\|u\|_\infty+\|u'\|_\infty,\qquad K_h=K_0+K_1.
$$

Both source norms are finite for $H^2$ inputs, and
$|h'|+|h|/2\le K_hD(u)e^{-b e^{2|x|}}$.
Keep the complete logarithmic discrepancy
$E(t)=\Psi(e^t)-e^t$, including every prime power. Define

$$
\begin{aligned}
\eta_0(t)&=
\begin{cases}
1,&0\le t<\log2,\\
9.39t^{1.515}e^{-0.8274\sqrt t},&t\ge\log2,
\end{cases}\\
M&=\sup_{t\ge0}\eta_0(t)<\infty,&
\bar\eta(R)&=\sup_{t\ge R}\eta_0(t),\\
J_b&=\int_{\mathbb R}e^{-y/2}e^{-b e^{2|y|}}dy<\infty.
\end{aligned}
$$

The published error gives $|E(t)|\le e^t\eta_0(t)$ on the whole
half-line. Its tail supremum $\bar\eta$ decreases to zero. Evenness
of the theta envelope gives the same $J_b$ with $e^{y/2}$.
No new counting or zero verification is needed.

For $x\ge0$ put $H_x(t)=h(x-t)+h(x+t)$. Reuse the
[signed Stieltjes interface](signed-discrepancy-window.md#a-fixed-row-tail-with-the-actual-complement-norm)
with this specified smooth row to obtain

$$
\begin{aligned}
\mathcal Ph(x)={}&\int_0^\infty e^{t/2}H_x(t)dt+2h(x)\\
&-\int_0^\infty E(t)e^{-t/2}
[H_x'(t)-H_x(t)/2]dt.
\end{aligned}
\tag{CP1}
$$

The endpoint $2h(x)$ comes from $E(0)=-1$ and is retained.
The theta envelope and bounded source derivatives justify these
integrals and the vanishing boundary at infinity; (RP1) already
supplies absolute convergence of the full prime action.
The continuous term in (CP1) becomes, on this same centered source,

$$
\int_x^\infty
[e^{(y-x)/2}-e^{-(y-x)/2}]h(y)dy.
\tag{CP2}
$$

Its absolute value is at most
$2K_0D(u)e^{x/2}J_{b/2}e^{-(b/2)e^{2x}}$.
Only the actual continuous main term was canceled; no signed
arithmetic remainder or prime power was removed.

## A decreasing envelope with its derivative cost

Split the discrepancy integral at $t=x/2$. Above that point,
$\eta_0(t)\le\bar\eta(x/2)$; changing variables in both translated
responses bounds its magnitude by
$2K_hD(u)e^{x/2}J_b\bar\eta(x/2)$.
Below that point both source arguments have magnitude at least $x/2$.
Integrating $e^{t/2}$ bounds this part by
$4K_hMD(u)e^{x/4}e^{-b e^x}$.
Together with (CP2) and the endpoint, put

$$
\begin{aligned}
\omega(R)={}&2K_hJ_b\bar\eta(R/2)
+4K_hM e^{-b e^R}\\
&+2K_0(J_{b/2}+1)e^{-(b/2)e^{2R}}.
\end{aligned}
$$

It is bounded, positive and decreasing to zero. Evenness extends the
complete response bound to the other half-line:

$$
|\mathcal P(su)(x)|
\le D(u)e^{|x|/2}\omega(|x|).
\tag{CP3}
$$

For large $R$, the published error envelope is decreasing and

$$
\omega(R)=O\!\left(R^{1.515}
 e^{-(0.8274/\sqrt2)\sqrt R}\right).
$$

This applies to exactly centered smooth sources, with the stated
extra derivative expense. It does not replace (RP1) on arbitrary
bounded sources or establish $\mathcal P(su)\in L^2$.

## Pay the positive-reserve cost on that same source

For $a,\delta>0$ use
$A=aK_0^2/\delta$, $\kappa=2b$ and
$T=\max\{1,\kappa^{-1}\log A\}$.
The existing weight comparison and substitution $t=e^{2|x|}$ give

$$
\int\frac{|s\mathcal P(su)|^2}{\delta+a s^2}dx
\le\frac{D(u)^2}{a}
\int_1^\infty t^{-1/2}\omega(\log t/2)^2
\min\{1,Ae^{-\kappa t}\}dt.
$$

Split at $\sqrt T$ and $T$. Monotonicity of $\omega$ and
$Ae^{-\kappa T}\le1$ bound the last integral by

$$
\begin{aligned}
\mathcal J(T)={}&2\omega(0)^2(T^{1/4}-1)\\
&+2(\sqrt T-T^{1/4})\omega(\log T/4)^2\\
&+\frac{\omega(\log T/2)^2}{\kappa\sqrt T}.
\end{aligned}
\tag{CP4}
$$

The final term uses the same exponential-tail integral as (RP2),
and also covers $T=1$. Consequently the allowance is
$D(u)^2\mathcal J(T)/a$, with $\mathcal J(T)=o(\sqrt T)$ as
$T\to\infty$. For fixed $a$ and a fixed centered $H^2$ source,
this upper allowance grows more slowly in order than the earlier
square-root logarithmic regulator allowance. This is no claim about
an actual inverse limit, useful numerical constants, endpoint exact
factorization or uniform gain for changing sources.

## Keep the original residual, parameter and coefficient map

For an arbitrary original even $H^2$ source, first use its exact
$\bar u=u-\langle u,v_0\rangle v_0$. Apply (CP3)--(CP4) to that
source in the existing (RP4) comparison, using the same low dual lift
and $r=QT_cu=QT_c\bar u$. Only the prime term is replaced:

$$
\langle r,C^{-1}r\rangle\le
3\left[4\varepsilon\|\bar u\|_2^2
+\frac{\|g_{\bar u}\|_2^2}{a_N}
+\frac{D(\bar u)^2\mathcal J(T_N)}{a_N}\right],
$$

where $T_N=\max\{1,\log(a_NK_0^2/\delta)/(2b)\}$ and all
$\varepsilon,c,\delta,N,a_N$ are the same original (WH1) choice.
The archimedean source and scalar costs remain present. Only the
residual-cost allowance vanishes on the exact ground column.
[SC14](sharp-center.md#retain-this-spatial-weight-in-the-complete-inverse-residual)
retains its separate trial contribution $C[q_0]$; the full inverse
allowances need not vanish.

For a common finite source family, a positive-semidefinite upper Gram $G_D$ must
certify $D(\sum z_i\bar u_i)^2\le z^*G_Dz$ and annihilate the
specified exact-ground coefficient. With canonical ground column
$u_0=v_0$, $d\operatorname{diag}(D(\bar u_i)^2)$ is one valid
choice, where $d$ is the number of source columns, paying that dimension
factor and retaining the zero ground row and column. The previous allowance remains available if its source
cost is smaller; an entrywise matrix minimum or independently chosen
column optima is not justified.

Growing or band-dependent families must pay their actual derivative,
source and archimedean Grams on one common sequence. The
prescribed-family cofinal existence is already supplied by the old
scalar floor and Fourier-tail convergence; no new existence theorem
is asserted here. Actual low and complementary-low signs, the original
critical remainder half-bound, full Robin, RH and Lean certification
remain unresolved.


## A high lift cannot hide the full low sphere's derivative cost

The derivative expense above cannot be made uniformly bounded on the
whole sharp-low unit sphere merely by choosing regular high trials.
Keep the original $P_N=\mathbf1_{|\mathsf D|<N}$, $Q_N=I-P_N$ and
real even unit ground $v_0\in H^2$. Classical smooth Fourier tests,
Plancherel scaling and weak integration by parts give the following
original-source application, without a new generic extension theorem
or Lean certificate.

Choose real odd Schwartz $g_1,g_2$ in two disjoint symmetric Fourier
bands strictly inside $0<|\xi|<1/2$, for example the positive bands
$(1/4,1/3)$ and $(2/5,1/2)$ and their negatives. Put $k_j=-g_j'$
and normalize $\|k_j\|_2=1$. The $k_j$ are real even, with disjoint
Fourier support. For $N>0$ use

$$
g_{j,N}(x)=g_j(Nx),\qquad k_{j,N}(x)=Nk_j(Nx)=-g_{j,N}'(x).
$$

These low-band $k_{j,N}$ are orthogonal and have norm $\sqrt N$.
Take a real unit vector $\alpha$ in the kernel of their two real ground
pairings. Such a vector exists even when both pairings vanish. Set

$$
k_N=\sum_j\alpha_jk_{j,N},\qquad
g_N=\sum_j\alpha_jg_{j,N},\qquad p_N=k_N/\sqrt N,\qquad
B_1=(\|g_1\|_1^2+\|g_2\|_1^2)^{1/2}>0.
$$

Then $p_N$ is real even Schwartz, $\|p_N\|_2=1$,
$p_N\in P_NH$, $p_N\perp v_0$, and $\|g_N\|_1\le B_1/N$.
It is fixed before choosing any high or ground correction. For every
$q\in Q_NH^2_{\rm even}$ and every complex scalar $t$, let
$u=p_N-q-tv_0$. Orthogonality and the declared pairing give

$$
\sqrt N=\langle u,k_N\rangle=\langle u',g_N\rangle,
\qquad \|u'\|_\infty\ge N^{3/2}/B_1.
\tag{DL1}
$$

This includes the actual exact-ground centering
$t=\langle p_N-q,v_0\rangle$. Therefore a common derivative upper
Gram on an isometric low coefficient frame containing $p_N$ has norm
at least $N^3/B_1^2$. Prescribed finite families need not contain this
witness. The quantified high trials are regular $H^2$ trials, rather
than the entire larger high form domain.

On the original WH1 sequence, (WF4) gives $\mu_\varepsilon\ge0$
and the inherited symbol bounds give
$\frac14\log(N/2)\le a_N\le13/2+\log N$ for large $N$.
Thus $T_N\to\infty$ and (CP4)'s first nonnegative term makes
$\mathcal J(T_N)\ge\omega(0)^2$ eventually. For this same input,
the displayed derivative-paid prime certificate is at least

$$
\frac{D(\bar u)^2\mathcal J(T_N)}{a_N}
\ge\frac{\omega(0)^2}{B_1^2}\frac{N^3}{13/2+\log N}
\longrightarrow\infty.
\tag{DL2}
$$

This diagnoses the size of that upper certificate, not the prime
response, actual inverse cost or form energy. The
[regulated L2 Schur budget](regulated-prime-source-budget.md#the-regulator-also-pays-an-l2-source-norm)
provides a different sufficient prime allowance on the same source.
The check above excludes uniform vanishing of the derivative-paid
certificate over the full low sphere; it leaves alternative budgets,
rough form trials, fixed-source families, actual cofinal signs and
RH/full Robin unresolved.
