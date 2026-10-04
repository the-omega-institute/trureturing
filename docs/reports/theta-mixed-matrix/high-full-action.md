# Actual full-Gamma high actions and whole-line matrix blocks

This experiment applies the original full Gamma symbol to the four
fixed $Z=QH_{1024,64}EB$ columns using their
[retained local source intervals](local-high.md). It reuses the
[off-grid/action allowances](off-grid-action.md) and
[localized Gram](local-z-gram.md). These are paper-model applications
with directed arithmetic, not new general methods or Lean certification.

Write $T_{\infty,64}$ for full Gamma with all prime powers through64,
$C_{64}=QT_{\infty,64}Q$ and $C=QTQ$ for the full prime operator.
The evaluated local source is

$$
H_Z=(T_{\infty,64}-\alpha I)Z,\qquad \alpha=1/8. \tag{HA1}
$$

Its definition does not alter the finite-$J=1024$ definition of $Z$.
The complete omitted-prime contribution is transported separately in
$L^2$, rather than inserted as a pointwise sample interval.

## Evaluate the action without another source solve

Read the saved $H,PH$ intervals, set $Z=H-PH$ on the core, and apply
the full digamma DFT to $sZ$. The physical period is128, spacing1/256,
and transform length32768. Each prime direction reads $Z(x\pm\log n)$
through (OA3), with the shifted finite kernel and its analytic error.
The exact-mean quadrature and its tail enter the original $cv_0$ term.
The original multiplication term remains exact.

The full-Gamma analytic allowance and numerical input balls both
enter the core $H_Z$ enclosure. Continuous sinc convolution, its paid
projection error, and numerical $H_Z$ balls give $PH_Z$ and $QH_Z$.
Zero padding evaluates finite sums; it does not replace the physical
projection by a frequency mask.

All1025 nonnegative core $H_Z,PH_Z$ rows are retained in
[high-full-action-samples.json](high-full-action-samples.json).
Evenness supplies negative rows. Rounded outward, the maximum local
column radii are below $6.797\cdot10^{-12}$ for $H_Z$ and
$2.133\cdot10^{-8}$ for $QH_Z$. These are column sample bounds,
not joint operator errors and not whole-line norm errors.

## Localize both whole-line integrals

Set $J=Z^*H_Z$ and $R_H=(QH_Z)^*(QH_Z)$. Orthogonal projection gives

$$
(R_H)_{ij}=\langle (H_Z)_i,(QH_Z)_j\rangle. \tag{HA2}
$$

Both integrands have a rapidly localized $H_Z$ factor. The real-even
holomorphic products have line $L^1$ bounds $U_\delta D_{H\mathcal Z}$
and $D_{H\mathcal Z}^2$. Their infinite-trapezoid errors are at most

$$
q_J=2U_\delta D_{H\mathcal Z}\frac r{1-r},\qquad
q_{R_H}=2D_{H\mathcal Z}^2\frac r{1-r}. \tag{HA3}
$$

Use the saved $Z_\infty$ from (LG3) and

$$
(QH_Z)_\infty\le
C_{H\mathcal Z}(2/b)^2e^{-2}
 +\sqrt{64/\pi}\,D_{H\mathcal Z}. \tag{HA4}
$$

The omitted lattice sums then cost $Z_\infty J_{H\mathcal Z}$ and
$(QH_Z)_\infty J_{H\mathcal Z}$. Thus no unpaid cutoff of a sinc tail
enters either whole-line integral. Scalar products of saved intervals
pay numerical errors without assuming their independence.

Because $Z$ is high,

$$
C_{64}Z=\alpha Z+QH_Z. \tag{HA5}
$$

With the existing $G_Z=Z^*Z$, the retained matrices are

$$
Z^*C_{64}Z=\alpha G_Z+J, \tag{HA6}
$$

$$
(C_{64}Z)^*(C_{64}Z)=\alpha^2G_Z+\alpha(J+J^*)+R_H. \tag{HA7}
$$

These are integrals of the actual whole-line vectors, rather than
matrices of the periodic screen that selected their coefficients.

## Pay the complete prime operator in the same matrices

Let $e_p=E_{p,64}\|Z\|$. The complete omitted-prime supplier and
sharp-$Q$ contraction imply $\|(C-C_{64})Z\|\le e_p$. Consequently

$$
\|Z^*CZ-Z^*C_{64}Z\|\le\|Z\|e_p, \tag{HA8}
$$

$$
\|(CZ)^*(CZ)-(C_{64}Z)^*(C_{64}Z)\|
\le2\|C_{64}Z\|e_p+e_p^2. \tag{HA9}
$$

The Hermitian maximum absolute row sum of (HA7) bounds
$\|C_{64}Z\|^2$. The resulting complete upper bound is

$$
\|CZ\|\le\|C_{64}Z\|+e_p<1.051588. \tag{HA10}
$$

The [result data](high-full-action-result.json) contains exact interval
endpoints for $J,R_H,Z^*CZ,(CZ)^*(CZ)$, separate analytic and omitted-prime
allowances, and the norm upper dyadics. The approximate full $Z^*CZ$ is

$$
\begin{pmatrix}
.2515687452&.1556162429&.0872290155&.0507020718\\
.1556162429&.3572862761&.1857425496&.1236059928\\
.0872290155&.1857425496&.3557725406&.2510440626\\
.0507020718&.1236059928&.2510440626&.6695465892
\end{pmatrix}.
$$

Only exact saved endpoints participate in bounds. The producer checks
24 representative direct shifted-sinc scalar sums against the padded
DFT and six transpose overlaps for each of the two localized matrices.
Source hashes identify data inputs; producer program bytes are not a
data-reuse condition. Valid input enclosures and paper estimates remain
premises, not facts established by parsing an arbitrary JSON payload.

```sh
uv run --no-project --python 3.13.12 --with python-flint==0.9.0 python docs/reports/theta-mixed-matrix/off_grid_action_bounds.py
uv run --no-project --python 3.13.12 --with python-flint==0.9.0 python docs/reports/theta-mixed-matrix/high_full_action.py
```

The producer is project-authored and uses python-flint/FLINT. It does
not rerun the original high-vector generation. The
[95 low actions and exact projected-ground direction](low-common-action.md)
and [common restricted comparison](restricted-schur.md) consume these
saved blocks. These four high action blocks alone prove no matrix sign,
cofinal, Robin or RH conclusion.
