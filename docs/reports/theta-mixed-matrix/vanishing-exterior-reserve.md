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

## The divided endpoint expression cannot have a strict weighted high floor

The next application concerns an actual proposed endpoint comparison,
rather than the multiplier allowance (VR2). Reuse the same analytic
uniqueness mechanism, the [theta derivative envelopes](../../../Library/Analytic/romik2021orthogonal.md#weighted-fourier-coefficient-suppliers)
(WC2), standard Fourier inversion and the Hahn--Banach annihilator
criterion for density. The inherited [minimal realization](../../../Library/Weil/fukushima2011dirichlet.md#transformed-form-and-a-global-derivative-comparison)
and [operator-domain interface](sharp-center.md#operator-domain-and-complete-block)
remain unchanged. This is a conditional paper/model application, without
a new generic density theorem, priority claim or Lean certification.

Fix a finite $N>0$ and an auxiliary $a>1/2$. Use the even complex space

$$
X_a=H^1_{\rm even}(\mathbb R)
\cap L^2(e^{2a|x|}dx),\qquad
\|h\|_{X_a}^2=\|h\|_{H^1}^2+\|e^{a|x|}h\|_2^2.
$$

This is a continuity topology for the divided endpoint expression
below. It is not the original minimal closed-form norm on the inputs
$q$. In particular, no density of sharp-high $q$ in that original
norm is asserted.

The images of the sharp-high original inputs are dense in this space:

$$
\overline{\{sq:q\in Q_NH^2_{\rm even}\}}^{\,X_a}=X_a.
\tag{VR5}
$$

To check the model mapping, let a continuous complex-linear functional
$\ell$ on $X_a$ annihilate these images. The bounds for both $s$ and
$s'$ in (WC2) make

$$
z\longmapsto s(x)\cos(zx)
$$

an $X_a$-valued entire function: each compact $z$ set and each parameter
derivative have integrable majorants in both parts of the $X_a$ norm.
Thus $F(z)=\ell(s\cos(zx))$ is entire. For smooth $\eta$ compactly
supported in $(N,\infty)$, the cosine packet

$$
q_\eta(x)=\int\eta(t)\cos(tx)dt
$$

is even Schwartz and belongs to $Q_NH^2$. The same majorants justify
the $X_a$-valued integral, so $\int\eta(t)F(t)dt=0$. Continuity makes
$F(t)=0$ for $t>N$; the existing identity theorem gives $F=0$.

For real $t$, $\|s\cos(tx)\|_{X_a}\le C_a(1+|t|)$. Schwartz
Fourier coefficients pay this majorant, so cosine Fourier inversion
gives $\ell(sq)=0$ for every even Schwartz $q$. Each even compact
smooth $h$ is $s(h/s)$, with $h/s$ again compact smooth because $s$
is positive and smooth. Cutoff and local mollification give the
standard compact smooth density in the full $X_a$ norm. Consequently
$\ell=0$, and the standard annihilator criterion gives (VR5).
Ordinary $L^2$ density alone would not supply this conclusion.

At $c=1/2$, write the divided endpoint expression as

$$
\begin{aligned}
\mathfrak q_{\rm end}(h)={}&
\langle m(\mathsf D)h,h\rangle+c_\Gamma\|h\|_2^2\\
&-\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}
\bigl[\langle\tau_{\log n}h,h\rangle
+\langle\tau_{-\log n}h,h\rangle\bigr]\\
&+\frac12\left|\int_{\mathbb R}2h(x)\cosh(x/2)dx\right|^2,
\qquad \tau_t h(x)=h(x+t).
\end{aligned}
\tag{VR6}
$$

Every prime power and both translated adjoints remain. The prime term
is an absolutely convergent bilinear series; no claim that the divided
prime action itself is in $L^2$ is needed. For $t\ge0$,

$$
|\langle\tau_{\pm t}h,g\rangle|
\le e^{-at}\|e^{a|x|}h\|_2\|e^{a|x|}g\|_2.
$$

Indeed $|x|+|x\pm t|\ge t$, and Cauchy--Schwarz pays the two
translated weighted factors. Hence both directions together are bounded
by $2\sum_{n\ge2}\Lambda(n)n^{-a-1/2}$ times the weighted norms.
This Dirichlet series converges for $a>1/2$. The logarithmic symbol
bound (WF3) controls the archimedean expression by the $H^1$ norm,
and $e^{-a|x|}\cosh(x/2)\in L^2$ controls the ground functional.
Thus (VR6) is continuous on $X_a$, without an endpoint positivity
assumption or a maximal-domain identification.

Use the original unit ground $v_0=2s\cosh(x/2)$ and

$$
T_{1/2}=\widetilde A-\tfrac12I
+\tfrac12|v_0\rangle\langle v_0|.
$$

Bounded parameter perturbation preserves the original minimal operator
domain. On every original even $H^2$ input, (WF1) and (SC1) give
exactly

$$
\langle T_{1/2}q,q\rangle=\mathfrak q_{\rm end}(sq).
\tag{VR7}
$$

The unweighted identity coefficient cancels at this parameter; the
rank-one coefficient in (VR6) is still $1/2$. The existing ground
identity gives $T_{1/2}v_0=0$. The same theta envelopes put
$h_0=sv_0\ne0$ in $X_a$ and give
$\mathfrak q_{\rm end}(h_0)=0$.

Consequently, no finite $N>0$ and $\kappa>0$ satisfy

$$
\langle T_{1/2}q,q\rangle\ge\kappa\|sq\|_2^2
\quad\text{for every }q\in Q_NH^2_{\rm even}.
\tag{VR8}
$$

For otherwise (VR5) supplies $h_j=sq_j\to h_0$ in $X_a$, with
each $q_j$ an actual sharp-high $H^2$ input. Continuity of (VR6)
and (VR7) would give $0\ge\kappa\|h_0\|_2^2>0$. This is a
fixed-band obstruction to a strictly positive $s^2$-weighted endpoint
floor. It supplies no negative energy, failure of endpoint
nonnegativity, RH counterexample, effective approximation cost or
moving-cofinal obstruction. The unweighted source norms are not
controlled by this density, so a positive subcritical exterior reserve
remains compatible with it. Actual common-sequence signs, the original
all-input half-bound and full Robin remain unproved.
