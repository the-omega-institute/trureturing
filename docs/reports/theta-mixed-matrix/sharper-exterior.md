# A sharper exterior row and transport to c=0.41

The [complete high-frequency comparison](joint-high-floor.md) uses a
saved interior floor of $0.4675789218114477$ on $[-3/2,3/2]$. Its
exterior lower bound is smaller. Applying the existing real
[root envelope](strip-root.md), rather than the coarser exterior
envelope, removes that bottleneck without evaluating theta, its 128
interior boxes, any action column or a matrix again. This is a
model-specific application of existing envelope and Schur methods.

## The full symmetric row on the exterior

At real $x$, (SR6) implies, for $u_x=e^{2|x|}$,

$$
s(x)\le C_su_xe^{-bu_x},\qquad
b=\pi/2,\qquad C_s^2=2\pi(7/6)(2\pi+3). \tag{SE1}
$$

Indeed $u_x\ge1$ and $u_x(2\pi u_x+3)\le(2\pi+3)u_x^2$.
For $y=x\pm\log n$, the triangle inequality and AM--GM give
$u_xu_y\ge n^2$ and $u_x+u_y\ge2n$. Split the exponential into
two equal parts and use $u_ye^{-bu_y/2}\le2/(be)$ to obtain

$$
s(x)s(y)\le C_s^2\frac2{be}e^{-bn}u_xe^{-bu_x/2}. \tag{SE2}
$$

The complete prime weights satisfy $\Lambda(n)/\sqrt n\le n$.
Summing every $n\ge2$ bounds all prime powers; including both shifts
and writing $r=e^{-b}$ gives

$$
R_B(x)\le
2C_s^2\frac2{be}\left(\frac r{(1-r)^2}-r\right)
u_xe^{-bu_x/2}. \tag{SE3}
$$

On $|x|\ge3/2$, $u_x\ge U=e^3$. Both $u_xe^{-bu_x/2}$ and
$u_x^2e^{-2bu_x}$ decrease there. Since $|c_\Gamma|<8$,

$$
W(x)\ge\frac12-R_{\rm ext}
-8C_s^2U^2e^{-2bU}, \tag{SE4}
$$

where $R_{\rm ext}$ is (SE3) evaluated at $U$. This exterior
estimate is not substituted for the interior row. The positive
$m(32)s^2$ term preserves (SE4) for $J_{32}$.

The [directed scalar producer](sharper_exterior.py) gives the
[saved high-gap supplier](sharper-exterior-result.json):

| Quantity | Directed bound |
|---|---:|
| $R_{\rm ext}$ | $<0.000022269131$ |
| Exterior $W$ floor | $>0.4999777308$ |
| Complete high form floor after saved leakage | $>0.4666471696633$ |
| $C(c_0)$ gap, $c_0=3/8$ | $>0.0916471696633$ |

The exterior floor exceeds the saved interior floor, so the interior
now determines the whole-line minimum. Subtracting the same saved
leakage upper bound gives the complete high form floor. No interior
sampling or supplier recomputation enters this step.

## Reuse the common residual with the stronger high gap

The actual $C$, $K$, $S$, trial columns, ground and restricted
comparison remain the same. Their existing conservative estimates
remain valid when a stronger coercivity bound for this same $C$ is
used in (TT5)--(TT9) of the
[quantified transport](threshold-transport.md). In particular the
old low-tail allowance and the old full-prime residual error are
retained, without replacing a retained block by a different operator.

The [transport result](sharper-threshold-transport-result.json) gives

$$
g(c_0)>0.03669425,\qquad
g(41/100)>0.00169425. \tag{SE5}
$$

These are conditional ground-orthogonal form gaps under the same
paper operator, exact-ground, domain and analytic supplier premises.
The exact zero ground is preserved. The range is bounded, not cofinal
as $c\uparrow1/2$; RH and the full Robin inequality remain unresolved.
There is no new general theorem, priority or Lean-certification claim.

## Reproduce the scalar refinement

```sh
uv run --no-project --python 3.13.12 --with python-flint==0.9.0 python docs/reports/theta-mixed-matrix/sharper_exterior.py
uv run --no-project --python 3.13.12 --with python-flint==0.9.0 python docs/reports/theta-mixed-matrix/threshold_transport.py --high-gap-supplier sharper-exterior-result.json --target-c 41/100 --output docs/reports/theta-mixed-matrix/sharper-threshold-transport-result.json
```

Both commands consume saved data. The programs are project-authored
and use python-flint/FLINT. The high-gap input is an explicit conditional
supplier whose source hashes and fixed-model fields are checked; it
does not certify the analytic premises by itself. Default transport
continues to use the original conservative high gap.
