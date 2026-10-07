# Reuse continuous sinc projection for the common weighted residual

This conditional numerical input sharpens the
[paid finite-core correction](weighted-residual-core.md) at the unchanged
$N=64$, $c=3/8$ realization. It reuses the existing continuous-sinc
projection, saved unprojected samples, cardinal integration kernel and
exact ground-frame construction. It acquires no operator samples and
does not reprove the underlying sampling or inverse results.

## Reconstruct the same source

Keep the same $95$ low columns $E$, four high columns
$Z=QH_{1024,64}EB$, dyadic correction $A$ and $\alpha=1/8$ as WR1.
Let $H=H_{1024,64}EB$ and form the unprojected common source

$$
F=H_L-(H_Z+\alpha H)A,\qquad QF=R_{64}.
\tag{SC1}
$$

The arrays contain $H_L,H_Z,H$ at $mh$, $0\le m\le1024$,
$h=1/256$. Their real evenness supplies negative input nodes.
The low/high actions have full Gamma and retained prime powers through
$64$; the source defining $H$ has $J=1024$. They remain distinct from
JW4's finite-$J$ actions.

Reuse [CP1–CP9](continuous-projection.md) and
[OA8–OA9](off-grid-action.md). For $0\le k\le414$, the finite
continuous projection gives

$$
B_k=F(kh)-h\sum_{m=-1024}^{1024}k_{64}((k-m)h)F(mh),
\qquad k_{64}(x)=\frac{\sin(64x)}{\pi x}.
\tag{SC2}
$$

Write $s_d=\sin(d/4)/(\pi d)$, with $s_0=1/(4\pi)$ and
$s_{-d}=s_d$. Fold each pair of equal input rows before computing:

$$
\theta_{k0}=\mathbf1_{k=0}-s_k,\qquad
\theta_{km}=\mathbf1_{k=m}-s_{k-m}-s_{k+m}\quad(m>0),
\qquad B_k=\sum_{m=0}^{1024}\theta_{km}F(mh).
\tag{SC3}
$$

This uses the continuous cutoff $64$, rather than a DFT frequency mask.
Only differences $0,\ldots,1438$ need kernel evaluation.

The CP hypotheses are inherited for the localized unprojected fields:
holomorphy with unused strip margin, integrable decay and the actual
line caps. The sharp projected residual itself is not called localized.
The wider OA7 cap also bounds unprojected $H$ through the SR12–SR13
construction; this does not reverse projection contraction.

The common alias and omitted-input-tail allowance is

$$
q_{CP}=q_{PH_L}+F_A(q_{PH_Z}+\alpha q_{PH}),
\quad q_{PH_L}=2D_lK_{64}\frac r{1-r}+\frac{64}{\pi}J_l,
\quad r=e^{-2\pi(1/8)/h}.
\tag{SC4}
$$

The saved complete $q_{PH_Z}$ and $q_{PH}$ already include their
localized omitted-input tails. They are not charged twice. Complete
omitted primes retain their separate WR7 transport.

## Keep source and arithmetic uncertainty

Let $l_{mj},z_{mt},h_{mt}$ be the saved unprojected component half-widths.
Select exact midpoint rows $\widehat F_m$ of SC1 and set

$$
e_{mj}=l_{mj}+\sum_{t=0}^{3}|A_{tj}|(z_{mt}+\alpha h_{mt}),
\quad \epsilon_F=\max_m\sqrt{\sum_{j=0}^{94}e_{mj}^2},
\quad a_{CP}=\max_k\sum_{m=0}^{1024}|\theta_{km}|.
\tag{SC5}
$$

All $1025$ input rows participate in this error, including those beyond
the shorter interpolation stencil. No source independence is assumed.

Evaluate SC3 with directed kernel coefficients and exact raw midpoint
rows. The resulting interval rows enclose the exact finite sum on
$\widehat F$. Choose exact dyadic midpoints of those intervals and pay
the maximum Euclidean row-radius norm $\epsilon_{\rm arith}$.
This includes kernel evaluation, raw midpoint representation and matrix
arithmetic. The common stencil-node error is at most

$$
\epsilon_{n}=a_{CP}\epsilon_F+\epsilon_{\rm arith}+q_{CP}.
\tag{SC6}
$$

Reuse the degree-$63$ cardinal polynomials and exact rational product
kernel from WR3–WR5 on the same $128$ cells. Their existing Bernstein
cap $\Lambda$ and Cauchy/de Boor remainder $\epsilon_{\rm an}$ give
$\epsilon=\epsilon_{\rm an}+\Lambda\epsilon_n$.
The program keeps the previously verified sufficient $\Lambda$; it
does not adopt unverified sharper reconstruction constants.

For $\beta=w_0-w\ge0$ on the core, retain $B=\max\beta$ and compute
its actual weight mass $\mu=6h\sum_{i=0}^{127}\beta_i$. The same
whole-line residual cap $\rho$ supplies

$$
\|D_{64}-D_{\rm poly}\|
\le 2\rho\sqrt{B\mu}\,\epsilon+\mu\epsilon^2.
\tag{SC7}
$$

Indeed, for each common unit coefficient vector,
$\|\sqrt\beta(R_{64}-p)\|_2\le\sqrt\mu\,\epsilon$ and
$\|\sqrt\beta R_{64}\|_2\le\sqrt B\,\rho$; the quadratic-form
difference gives SC7. The same actual coefficient vector is kept
through both norms and the polynomial integral.

## Retain the original inverse and frame obligations

WR7–WR8 apply unchanged: add the full-prime core transport, round the
sum of published error components outward once, and subtract that
fixed scalar cap on the true $94$-direction ground frame. Its component
uncertainties and every cross entry remain present. The scalar baseline
prime charge and RS8 trial-form prime charge are still paid separately.
The output entry intervals enclose one Hermitian gain matrix; entrywise
lower endpoints do not form a Loewner lower matrix.

The [directed output](sinc-weighted-residual-core-result.json) has these
rounded outward bounds under the inherited mathematical suppliers:

| Quantity | Bound |
|---|---|
| Common raw source row error | $<7.424744\cdot10^{-12}$ |
| Folded sinc coefficient amplification | $<3.797909$ |
| Kernel and row arithmetic error | $<1.438347\cdot10^{-56}$ |
| Common CP continuum projection error | $<3.020489\cdot10^{-73}$ |
| Total interpolation point error | $<1.397958\cdot10^{-10}$ |
| Core integration/input and prime error cap | $<8.480901\cdot10^{-11}$ |
| Restricted gain trace | $>0.00086366172097531$ |
| Gain on frame column indexed $2$ from zero | $>0.00020431849666045$ |

The core error cap is about $1069$ times smaller than the saved projected
sample route's cap. This compares error allowances, not inverse values
or a uniform gain. On the same frame column $2$, the new gain lower
endpoint exceeds the old gain upper endpoint by more than
$9.061349\cdot10^{-8}$. That lowers the computed scalar upper allowance
on this named direction; it does not establish Loewner domination on
all directions or positive semidefiniteness of the gain matrix.

The conditional global $0.4605$ comparison is not recalculated.
The all-input half-bound, complementary-low estimate and actual joint
signs on one cofinal sequence, full Robin, RH and Lean certification
remain unresolved. Hash and parameter checks identify the realization;
they do not discharge its original-model premises.

From the repository root:

```sh
uv run --no-project --python 3.13.12 --with python-flint==0.9.0 python docs/reports/theta-mixed-matrix/weighted_residual_core.py --reconstruction sinc
```

The [existing integration program](weighted_residual_core.py) calls
[the new saved-row reconstruction](sinc_residual_rows.py).
The default saved-projection route and its existing result are retained.
Both programs are project-authored and use python-flint/FLINT under
their dependency licenses. No old producer, action solve or LDL is run.
