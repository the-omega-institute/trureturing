# The vanishing exterior reserve on the original sharp high space

The existing [scale-dependent high supplier](../../../Library/Weil/fukushima2011dirichlet.md#spatially-weighted-high-inverse-at-every-subcritical-parameter)
already gives a positive high restriction at each prescribed subcritical
parameter. The [common dual-source construction](sharp-center.md#pay-weighted-action-errors-with-one-common-dual-source)
already retains the sharp projection and exact ground jointly. Neither
construction needs a new general Schur or Fourier theorem. The remaining
interface concerns their actual source budgets as the parameter changes.

This note applies classical Fourier-Laplace analyticity, the existing
[identity-theorem anchor](../../../Library/Zeros/jaiswar2021identity.md)
and Fourier injectivity to the original theta weight. The
[critical-remainder support check](../../../Library/Weil/lagarias2004li.md#compact-support-does-not-survive-this-projection)
already uses this analytic uniqueness mechanism on a different space.
Here the application concerns the sharp Fourier high space. It is a
paper application with the inherited coefficient and realization premises,
without a numerical experiment, new generic theorem, priority claim or
Lean certification.

## A fixed sharp-high residual cannot use the zero-reserve weight

Keep $s=\sqrt{\Phi/(2\cosh(x/2))}>0$, the original even $L^2(dx)$
space, and $Q_N=\mathbf1_{|\mathsf D|\ge N}$ for fixed $N>0$.
The [original-series coefficient envelope](../../../Library/Analytic/romik2021orthogonal.md#weighted-fourier-coefficient-suppliers)
supplies, for fixed $K,b>0$,

$$
s(x)\le K\exp(-b e^{2|x|}). \tag{VR1}
$$

For any fixed finite $a>0$ and any nonzero $r\in Q_NL^2(dx)$,
the corresponding zero-reserve multiplier allowance is infinite:

$$
\int_{\mathbb R}\frac{|r(x)|^2}{a s(x)^2}\,dx=\infty.
\tag{VR2}
$$

Here nonzero means nonzero as an $L^2$ equivalence class. No pointwise
smoothness, compact support or operator-domain assumption on $r$ is used.

To check this application, suppose the integral were finite. For every
$B>0$ and nonnegative integer $k$, Cauchy--Schwarz and (VR1) give

$$
\int_{\mathbb R}(1+|x|)^k e^{B|x|}|r(x)|\,dx
\le\|r/s\|_2
 \|s(1+|x|)^k e^{B|x|}\|_2<\infty. \tag{VR3}
$$

Consequently the absolutely convergent Fourier-Laplace integral
$\mathcal L_r(z)=\int r(x)e^{-izx}dx$ is entire: on every compact
$z$ set the integrand and its complex derivative have an integrable
majorant from (VR3). On the real line it is the continuous $L^1$ Fourier
transform and agrees almost everywhere, up to the unitary normalization,
with the $L^2$ transform. The sharp-high condition makes that transform
zero almost everywhere on $(-N,N)$. Continuity makes it zero on the
whole interval; the identity theorem and Fourier injectivity then give
$r=0$ almost everywhere, a contradiction.

This is the usual analytic uncertainty mechanism applied to (VR1).
The repository's [compact-support Paley--Wiener declaration](../../../D5/S3/Fourier/PaleyWiener.lean)
has a different hypothesis and is not invoked for this noncompact source.
The [strip Fourier source](../../../Library/Analytic/tao2021stripfourier.md)
likewise retains its own strip-decay hypotheses; they are not assumed
for a sharp projection. Here (VR3) supplies the required integral
majorants directly.

## The order of limits matters

For this same fixed $N,a,r$, define the finite subcritical allowance

$$
I_\delta(r)=\int_{\mathbb R}
 \frac{|r(x)|^2}{\delta+a s(x)^2}\,dx,
\qquad \delta>0.
$$

It obeys $I_\delta(r)\le\delta^{-1}\|r\|_2^2$. Monotone convergence
and (VR2) give

$$
I_\delta(r)\longrightarrow\infty\qquad(\delta\downarrow0).
\tag{VR4}
$$

The parameters in (WH1)--(WH2) instead move together:
$\delta_j=\varepsilon_j/4$, $N_j\ge N_w(\varepsilon_j)$,
$a_j=m(N_j/2)-\mu_{\varepsilon_j}$, with sources chosen at those
same bands. Formula (VR4) gives no rate or divergence conclusion for
$I_{\delta_j}(r_j)$ when $a_j,N_j,r_j$ change. In particular the
fixed-band [paid sinc residual](sinc-weighted-residual-core.md) keeps a
strictly positive exterior reserve and is unaffected by this obstruction.
The exact ground column has residual zero and is excluded from (VR2).

## Use the existing constrained source interface

The simple integral is only an upper allowance for the true high inverse.
Its divergence does not imply that $\langle r,C^{-1}r\rangle$ diverges,
that the actual operator loses positivity, or that an endpoint high
comparison has been established. No zero-reserve high lower form is
assumed here.

The existing (SC19)--(SC20) instead minimizes over low additions to the
same high source, with the exact ground term in the inverse, and permits
the common unprojected action as a specified dual trial. That trial is
already available and should be reused. Removing the projection alone
does not prove that its full arithmetic action divided by $s$ is in
$L^2$, or bound its changing coefficient and derivative Grams.

The remaining work is therefore to bound the actual common source/trial
Grams and truncation errors on the same $\varepsilon_j,N_j$ sequence,
and to obtain the low and complementary-low lower signs that pay those
costs. Taking the zero-reserve multiplier limit first cannot supply
those estimates. The original all-input half-bound, common cofinal
positivity, RH and full Robin remain unresolved.
