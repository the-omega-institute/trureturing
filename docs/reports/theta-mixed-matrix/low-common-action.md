# Actual low actions and localized mixed blocks

This paper-model computation evaluates the95 unweighted low-band inputs
of the existing [Legendre trial basis](high-trials.md), their full-Gamma
actions with primes through64, and the whole-line low/mixed matrices.
It reuses the [saved high actions](high-full-action.md), rather than
regenerating their source vectors. Fourier inversion, Poisson summation
and directed ball arithmetic are existing methods. No new general
method or Lean certification is claimed.

Keep $c=3/8$, $\alpha=1/8$, $P=P_{64}$, $Q=I-P$, the exact isometry
$E:\mathbb R^{95}\to PL^2_{\rm even}$ and the saved
$Z=QH_{1024,64}EB$. The retained action $T_{64}=T_{\infty,64}$ has
full Gamma and every prime power through64. This does not change the
finite-$J=1024$ definition of $Z$.

## Low-input analytic allowances

On one95-dimensional coefficient unit ball the band-limited inputs have
contour caps

$$
U_l=e^8,\qquad U_w=e^{64(7/48)}. \tag{LA1}
$$

The accepted [full-Gamma estimates](full-gamma-periodic.md) are linear
in the input contour cap. Their transport to (LA1) uses the exact saved
high cap as a denominator. It does not assume that low inputs belong
to the four-column high family. At width $1/8$, the low action line
bound uses the same wider width $7/48$, multiplier envelope and margin
$1/48$ as [OA8](off-grid-action.md). The real mean bound is fixed before
transporting its output $v_0$ to a contour.

The [scalar allowance data](low-full-action-coefficients.json) is produced
by [low_full_action_coefficients.py](low_full_action_coefficients.py).
Its rounded outward bounds include

| Quantity | Upper bound |
|---|---|
| Full-Gamma low core analytic error | $2.679\cdot10^{-17}$ |
| Low $H$ contour-line $L^2$ norm | $715480$ |
| Continuous $PH$ analytic error | $1.629\cdot10^{-78}$ |
| Ground moment quadrature and tail | $5.425\cdot10^{-84}$ |
| Low $H$ physical/lattice $L^1$ tail | $2.750\cdot10^{-2020}$ |

These are analytic supplier allowances. Numerical basis, DFT,
prime-shift and product balls remain separate.

## Enclose the exact projected-ground direction

The [moment producer](exact_ground_moments.py) computes

$$
e=E^*Pv_0=E^*v_0, \tag{LA2}
$$

using the inherited normalized DLMF spherical-Bessel formula, anchors
94/95, backward recurrence, phase factors and the removable value at
zero. The finite trapezoid sum receives the (LA1) contour quadrature
and localized tail allowance. All95 component intervals are saved in
[exact-ground-moments-result.json](exact-ground-moments-result.json).
Their joint norm enclosure lies strictly between zero and one; its
deficit from one is about $2.65753850\cdot10^{-39}$. This is an
enclosure of the actual direction, not a replacement by a floating
near-nullvector. The [restricted matrix computation](restricted-schur.md)
transports every component interval into its frame.

## Evaluate95 actions on the common source

Define

$$
H_L=(T_{64}-\alpha I)E,\qquad
H_Z=(T_{64}-\alpha I)Z. \tag{LA3}
$$

The [action producer](low_common_action.py) generates the unweighted95
basis values once on the1025 nonnegative core points, uses one common
full digamma symbol on the32768-point DFT, and processes each column's
transform separately. The period is128 and spacing is1/256. Prime
shifts use direct low-basis values at $x\pm\log n$, rather than
off-grid reconstruction of the high family. The exact mean intervals
(LA2), original multiplication term and analytic core allowance enter
$H_L$. Continuous sinc convolution and its allowance give $PH_L$;
zero padding computes finite sums and is not a frequency-mask projection.

The [saved core data](low-common-action-samples.json) retains all95
$H_L,PH_L$ columns. Each endpoint pair is an integer pair multiplied
by $2^{-80}$; lower endpoints are rounded down and upper endpoints up.
This is an additional outward enclosure. The matrices below use the
original Arb balls before this serialization. The maximum local
column radii before serialization are below $2.679\cdot10^{-17}$ for
$H_L$ and $8.403\cdot10^{-14}$ for $QH_L$. These are column sample
radii, not joint operator errors.

## Localize every whole-line matrix product

Write $K_{64}=QT_{64}E=QH_L$. The evaluated blocks are

$$
T_{LL}^{64}=\alpha I+E^*H_L,\quad
KK=K_{64}^*K_{64}=\langle H_L,QH_L\rangle, \tag{LA4}
$$

$$
J=K_{64}^*Z=\langle H_L,Z\rangle,\quad
M=K_{64}^*C_{64}Z=\alpha J+\langle H_L,QH_Z\rangle. \tag{LA5}
$$

Here $C_{64}=QT_{64}Q$. Orthogonal projection makes each identity
hold for the actual common vectors. Every integral has a localized
$H_L$ factor; the full sinc tails of its partner remain present.

Let $D_l,D_h,U_h$ be the saved contour caps of $H_L,H_Z,Z$, let $J_l$
be the low localized omitted-lattice $L^1$ allowance, and set
$r=e^{-2\pi(1/8)/h}$. The four line-product caps are respectively
$U_lD_l,D_l^2,D_lU_h,D_lD_h$. Their infinite-trapezoid errors are
twice these caps times $r/(1-r)$. Sharp Fourier projection commutes
with contour weighting and is contractive on these line $L^2$ norms.

For the finite-lattice omissions multiply $J_l$ by the partner's real
supremum: $\sqrt{64/\pi}$ for $E$, the saved real bound for $Z$, and

$$
\|QH_L\|_\infty\le\|H_L\|_\infty+\sqrt{64/\pi}D_l,
\qquad
\|QH_Z\|_\infty\le\|H_Z\|_\infty+\sqrt{64/\pi}D_h. \tag{LA6}
$$

Scalar products of the actual numerical balls pay arithmetic uncertainty
without independence assumptions. The [result data](low-common-action-result.json)
saves all four whole-line blocks, separate quadrature/tail allowances,
source hashes and4,465 transpose-overlap checks for each symmetric
block. Transpose checks verify consistency; the analytic premises and
interval arithmetic carry the enclosures.

## Reproduce and scope

```sh
uv run --no-project --python 3.13.12 --with python-flint==0.9.0 python docs/reports/theta-mixed-matrix/low_full_action_coefficients.py
uv run --no-project --python 3.13.12 --with python-flint==0.9.0 python docs/reports/theta-mixed-matrix/exact_ground_moments.py
uv run --no-project --python 3.13.12 --with python-flint==0.9.0 python docs/reports/theta-mixed-matrix/low_common_action.py
```

The project-authored programs use python-flint/FLINT. Already valid saved
suppliers can be reused without rerunning their generators. Data hashes
bind the common inputs; producer program hashes are not reuse conditions.
The complete omitted-prime allowance is a whole-$L^2$ operator bound,
paid in [the joint matrix comparison](restricted-schur.md), not in these
local primes-through64 samples. Parsing an arbitrary JSON payload does
not establish its analytic premises. These actions and mixed blocks
alone supply no matrix sign, cofinality, Robin or RH conclusion.
