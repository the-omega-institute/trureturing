# Actual Robin kernel in a common ratio window

The [consumer](robin_kernel_ratio.py) reads the exact dyadic endpoints in the
existing [complete diagonal data](robin-kernel-diagonal.json). It does not
recompute Binet coefficients, their derivative tails, inverse coefficients,
PNT bounds or prime panels. The [ratio data](robin-kernel-ratio.json) record
the source hash, directed derived parameters and strict integer allowance.

The manuscript's analytic profile in
[FIB §399](../../develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md#399-共同比例尺度的实际核轮廓符号转折与同源窗口预算) is

$$
p(u)=\frac A2u^2+(D-A)u+c_{\mathrm{diag}},\qquad u=\log(s/x).
$$

The existing source intervals verify $D-A>0$ and $c_{\mathrm{diag}}<0$.
The consumer encloses the unique positive root and its scale ratio:

$$
u_*\approx0.01943486591757688819,
\qquad e^{u_*}\approx1.01962495236207035243.
$$

These are roots of the limiting profile, not finite-x locations of a kernel
zero. The manuscript supplies that connection through a uniform error and
global monotonicity estimate; neither analytic application is Lean verified.

For $\ell=\log x\ge1$ and $0\le u\le U$, its allowance is

$$
|\ell\mathcal G_x(\ell+u)-p(u)|\le\frac{C(U)}\ell,
\qquad
C(U)=\frac A6U^3+\frac D2U^2+(2D-A)U+D+\mu_0(2U+11).
$$

The scalar calculation uses the inherited bound
$\mu_0\le2205/(94q)$ from FIB §384, rather than recomputing an inverse norm.
At $u_-=1/100$ and $u_+=3/100$, the supplied directed intervals pay the
profile signs, error allowances and monotonicity condition with the common
strict integer threshold

$$
\log x\ge109389.
$$

Conditional on the manuscript's analytic estimates, this yields a negative
kernel for $x\le m$ and $m+1\le e^{1/100}x$, and a positive kernel for
every $m\ge e^{3/100}x$. The threshold is extremely large and is not
claimed sharp. The integer ceiling is taken from an exact outward dyadic
endpoint with strict slack; no binary-float threshold is used.

The same source carries a finite ratio-window approximation

$$
\left|\sum H_mJ_x(m)-\frac1\ell\sum H_m\Pi_x(m)\right|
\le C(U)U\min\left\{\frac{310}{441\ell^2},\frac{C_H}{\ell^6}\right\},
\qquad
\Pi_x(m)=\int_m^{m+1}\frac{p(\log(s/x))}{s^2}\,ds,
$$

where both sums use precisely $x\le m$ and $m+1\le e^Ux$.
This bounds the approximation error, not the signed profile sum itself.
Both bounds apply to the same actual H sequence. The explicit constant
$310/441$ reuses the inherited trivial Mertens and Binet budgets, so that
bound requires no numerical $C_H$ certificate. The stronger inverse-log
order keeps its existing unspecified $C_H$; neither bound pays the full
critical Robin scale.

## Reproduction

The entry requires the sibling `robin_kernel_diagonal.py` for the existing
dyadic exporter, Python 3.13 and python-flint 0.9.0. The declared offline
runtime must be installed or cached.

```sh
uv run --offline --no-project --python 3.13 --with python-flint==0.9.0 python docs/reports/fib-robin-boundary/robin_kernel_ratio.py --source docs/reports/fib-robin-boundary/robin-kernel-diagonal.json --output /tmp/robin-kernel-ratio.json
```

The result uses 192 bits; the consumer accepts a precision parameter of
at least 128 bits. On macOS arm64, the entry and sibling import were
exercised from another working directory with spaces in producer, input
and output paths, a disabled login shell and 128 bits; other platforms
were not exercised. It makes no full-H sign assertion, no Robin or RH
conclusion and no new formal proof of the existing source intervals.
