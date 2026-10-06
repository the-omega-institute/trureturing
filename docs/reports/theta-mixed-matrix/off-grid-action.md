# Off-lattice high inputs and full-Gamma action transport

The vectors remain $Z=QH_{1024,64}EB$ and $g=Qv_0$. This application
reuses the [strip supplier](strip-root.md),
[continuous sinc projection](continuous-projection.md),
[actual real norm](local-z-gram.md) and
[full-Gamma periodization allowance](full-gamma-periodic.md).
Fourier inversion, Poisson summation and weighted Plancherel are the
existing tools; no new general theorem or Lean certification is claimed.

Set $h=1/256$, $X=4$, $R=128$, $\delta=1/8$, $\nu=\pi/h$ and
$r=e^{-2\pi\delta/h}$. Write $k_N(t)=\sin(Nt)/(\pi t)$ with
$k_N(0)=N/\pi$. All coefficient norms below refer to one specified
family, rather than independently chosen extremizers.

## Read prime shifts from the localized source

Let $U_H=D_\delta F_B$ be the saved line bound for $H=H_{1024,64}EB$.
The two contour bounds give the weighted Fourier $L^2$ allowance
$\sqrt2 U_H$. Hence

$$
\|H-P_\nu H\|_\infty
\le\frac{U_He^{-\delta\nu}}{\sqrt{\pi\delta}}. \tag{OA1}
$$

The existing sinc/Poisson calculation at cutoff $\nu$ costs

$$
q_\nu=2U_HK_\nu\frac r{1-r},\qquad
K_\nu=\sqrt{\frac{\sinh(2\nu\delta)}{2\pi\delta}}. \tag{OA2}
$$

If $J_X$ is the saved omitted physical/lattice $L^1$ bound for $H$,
the finite-input tail costs $(\nu/\pi)J_X$. Combine this with the
saved cutoff64 projection allowance $q_{64}$:

$$
Z(x)=h\sum_{|jh|\le X}H(jh)
 [k_\nu(x-jh)-k_{64}(x-jh)]+\epsilon(x), \tag{OA3}
$$

$$
\|\epsilon\|_\infty\le
\frac{U_He^{-\delta\nu}}{\sqrt{\pi\delta}}
 +q_\nu+\frac\nu\pi J_X+q_{64}<5.281\cdot10^{-35}. \tag{OA4}
$$

This holds for arbitrary real $x$, including $x\pm\log n$.
Numerical source intervals and kernel arithmetic are separate inputs
to the finite sum. An unshifted DFT readout is not an off-grid value.

For a positive prime shift $\tau=\log n$, tabulate the finite kernel
$k_\nu(mh+\tau)-k_{64}(mh+\tau)$. At the local outputs,
$|m|\le2048$. Zero padding with length32768 computes the exact
finite sum, without replacing the continuous projection by a mask.
Evenness supplies $Z(x-\tau)$ from the positive-shift convolution at
output $-x$. The cardinal numerator simplifies exactly to
$\sin(\nu(mh+\tau))=(-1)^m\sin(\nu\tau)$; the cutoff64 numerator
uses the angle-addition formula at $m/4+64\tau$.

## Transport the full action on the same family

Put $\mathcal Z=(g,Z)$ and $H_{\mathcal Z}=(T_{\infty,64}-\alpha I)
\mathcal Z$, where $T_{\infty,64}$ uses full Gamma and all prime powers
through64. It keeps the exact multiplication and mean terms.
Let $L_0,C_m$ be (FG1), (FG4), and
$R_{\rm real}\ge\|\mathcal Z\|$ be (LG5). With
$C_s=\sqrt{2\pi(7/6)(2\pi+3)}$, the real envelope is

$$
|H_{\mathcal Z}a(x)|\le C_{H\mathcal Z}u^2e^{-bu}\|a\|,
\quad u=e^{2|x|},\quad b=\pi/2, \tag{OA5}
$$

$$
C_{H\mathcal Z}=C_s[C_m+(8+2W_{64})A_0L_0+2cR_{\rm real}].
$$

The factor $2cR_{\rm real}$ uses the exact real mean and
$\|v_0\|_2=1$. Thus both physical and omitted-lattice tails are paid by

$$
J_{H\mathcal Z}=C_{H\mathcal Z}e^{-bU_X}
 (U_X/b+1/b^2),\qquad U_X=e^{2X}. \tag{OA6}
$$

To bound the full logarithmic multiplier on a contour, use the
existing envelope formulas at $\delta'=7/48$ and margin
$\varepsilon=\delta'-\delta=1/48$. Write the wider root/ground bounds
as $A',V'$ and

$$
D'_{\rm ret}=A'^2(M_{1024}+8+2W_{64})e^{64\delta'}+cV',
\quad U'=\sqrt{V'^2+(D'_{\rm ret}F_B)^2}. \tag{OA7}
$$

These bound the same fixed $g,Z$. For the existing symbol envelope
$G(t)=4+\tfrac12\log(1+4t^2)$, its derivative bound gives
$\sup_{t\ge0}G(t)e^{-\varepsilon t}\le G(12)$. Weighted Plancherel,
then multiplication by the outer $s$, gives the contour allowance

$$
D_{H\mathcal Z}=A_\delta\sqrt2G(12)A'U'
 +A_\delta^2(8+2W_{64})U_\delta
 +cR_{\rm real}V_\delta. \tag{OA8}
$$

The mean coefficient is fixed on the real line before its output
$v_0$ is transported. The same sinc calculation and the localized
envelope now give

$$
q_{PH\mathcal Z}=2D_{H\mathcal Z}K_{64}\frac r{1-r}
 +(64/\pi)J_{H\mathcal Z}<4.213\cdot10^{-73}. \tag{OA9}
$$

The real mean quadrature/tail allowance is

$$
q_\mu=2V_\delta U_\delta\frac r{1-r}
 +2C_sL_0e^{-bU_X}(U_X/b+1/b^2). \tag{OA10}
$$

Combine its $cv_0$ output with the saved full-Gamma local allowance.
Numerical samples, special functions and finite arithmetic remain
separate. The propagated off-grid prime-input allowance is below
$4.142\cdot10^{-33}$.

The [complete omitted-prime supplier](forward-action.md) is a
whole-$L^2$ operator allowance, so it applies to this high family:
$\|(T-T_{\infty,64})\mathcal Z\|\le E_{p,64}R_{\rm real}
<9.376\cdot10^{-19}$. This is not a pointwise tail bound.

The [directed coefficients](off-grid-action-result.json) are produced by
[off_grid_action_bounds.py](off_grid_action_bounds.py). Its strip-width
guard uses exact rational comparisons before conversion to Arb.

```sh
uv run --no-project --python 3.13.12 --with python-flint==0.9.0 python docs/reports/theta-mixed-matrix/off_grid_action_bounds.py
```

The [four-column action](high-full-action.md) uses these inputs.
The coefficients alone supply no numerical action, common residual
Gram, restricted Schur sign, cofinality, Robin or RH conclusion.
