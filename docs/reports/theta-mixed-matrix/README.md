# Actual mixed theta scalar assembly

This program evaluates the documented
[complete theta matrix assembly](../../../Library/Weil/jarohsweth2020local.md)
on one specified real even trial function. It retains the original
probability measure, Gamma jump corners, all retained prime powers and
full-probability variance. Its purpose is to exercise that implementation
interface; this single function is not the complete approximation family
required by the fixed-window spectral test.

## Exact inputs and model

Put $\ell=\log2$, $\delta=1/2$ and

$$
b(x)=2w_{1/2}(x)=\frac{\mathbf1_{\{1/2<|x|<1\}}}{\ell|x|}.
$$

The target is
$T=D(b)-(3/8)(G-\mu^2)$, with $G=\int b^2d\nu$,
$\mu=\int b\,d\nu$, $d\nu=2\Phi(x)\cosh(x/2)dx$ and total mass one.
The original theta series and the exact weight
$\psi(t)=e^{-t/2}/(1-e^{-2t})$ are used.

The retained Gamma square is $[-2,2]^2$. Complete positive-shift prime
terms are retained through $N=8$: $2,3,4,5,7,8$, with
$w_{p^k}=\log p/\sqrt{p^k}$. Each positive-shift integral includes both
original graph directions in the normalized energy.

Gamma cells have boundaries $-2,-1,-1/2,1/2,1,2$. The two nonzero
same-cell triangles, eight jump-corner triangles and three separated
rectangles cover every nonzero retained contribution. Each transformed
unit square uses $64^2$ directed interval boxes, totaling 53,248 boxes.
The jump differences are kept in their one-sided branches. No nested
analytic integral is used.

The six-term theta callback includes the uniform complex remainder from
(TH) in the model note and rejects boxes violating its strip or ratio
conditions. The real removable kernel uses the positive entire series
for $\sinh(t)/t$ through order 20 with a geometric remainder. Field
multiplication encloses real squares even when their intervals cross
zero. Shifted prime breakpoint ordering and both active and zero branch
membership are explicitly certified; ambiguity raises an error.

## Directed target accounting

Choose the exact rounded dyadic $r$ saved in the result. The retained
quantity is

$$
F_r=D_{2,8}(b)-\tfrac38(G-2\mu r+r^2),
\qquad
T-F_r=R_\Gamma+R_p+\tfrac38(\mu-r)^2\ge0.
$$

The reported upper bound for the full $T$ adds both explicit omitted-tail
bounds and the mean loss. In particular, the upper endpoint of $F_r$
alone is not an upper bound for $T$. Since $\log9>2$ is certified, the
omitted prime supports are disjoint and the coefficient-one potential
bound applies. Every omitted prime power is included in that bound.

The result contains exact dyadic lower/upper endpoints, the actual runtime
versions, every retained prime term and Gamma panel, and the number of
certified branch reads. Rounded human-readable intervals are:

| Quantity | Enclosing interval or upper bound |
|---|---|
| $G$ | $[0.1173319675831936,0.1173319675831938]$ |
| $\mu$ | $[0.0448861392452370,0.0448861392452372]$ |
| $D_{p,\le8}(b)$ | $[0.0206720399437825,0.0206720399437827]$ |
| $D_{\Gamma,[-2,2]}(b)$ | $[0.0295399,0.0485488]$ |
| $F_r$ | $[0.0069680,0.0259769]$ |
| $R_\Gamma$ | $<3.7720\cdot10^{-38}$ |
| $R_p$ | $<2.2821\cdot10^{-6}$ |
| $(3/8)(\mu-r)^2$ | $<7.5872\cdot10^{-14}$ |
| Full $T$ | $[0.0069680,0.0259792]$ |

This directed computation gives a positive lower bound on this scalar
trial target. It does not supply signs for the prescribed full family,
a complete low-spectral-window exclusion, a cofinal window certificate,
Lean certification, RH or the full Robin inequality.

## Reproduce

The recorded runtime is Python 3.13.12, python-flint 0.9.0, FLINT 3.6.0,
with 128-bit ball arithmetic. The inspected source-method documentation
is separately pinned in the
[Johansson integration note](../../../Library/Analytic/johansson2018ballintegration.md);
its FLINT 3.3.1 documentation pin is not a claim about the installed wheel.

```sh
uv run --no-project --python 3.13.12 --with python-flint==0.9.0 python docs/reports/theta-mixed-matrix/scalar_pilot.py
```

The command writes `scalar-result.json` next to the program. Nonfinite
enclosures, uncertified branches or breakpoint ordering, failed tail
conditions and the declared box limit reject the computation. The
implementation uses existing FLINT directed arithmetic and integration;
no third-party implementation code is copied here. The program is
project-authored; dependency licensing is supplied by python-flint/FLINT.
