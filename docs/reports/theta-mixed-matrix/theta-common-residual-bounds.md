# Actual common-source residual for the quadratic input

This is a conditional paper application and directed numerical experiment
for the [actual negative-edge operator and common critical-source inverse](../../../Library/Weil/lagarias2004li.md#even-geometry-gives-a-stronger-negative-edge-inverse-constant).
It reuses the critical directions, individual certified real Xi zeros,
derivative-polynomial recurrence, FLINT ball arithmetic and
[validated integration supplier](../../../Library/Analytic/johansson2018ballintegration.md).
No new generic integration, projection or spectral theorem is claimed.
The computation concerns the bounded operator $B$, without asserting
original form-domain membership of the input $h(x)=x^2$.

Write

$$v_k=\Phi^{(2k)}/\Phi-4^{-k},\qquad
f=x^2-\sum_{k=1}^7 a_kv_k,\qquad
w=\sum_{j=1}^8 b_j\frac{\cos(\gamma_jx)}{\cosh(x/2)}.$$

The exact dyadic coefficients are in
[the fixed candidate](theta-common-residual-candidate.json). Each
$\gamma_j$ comes from `acb.zeta_zero(j)` as a ball, with no double rounding.
Thus $n=\sum a_kv_k\in N$ and $w\in N^\perp$ by the inherited supplier
premises, without zero-family completeness or RH.

The [whole-space result](theta-common-residual-bounds-result.json) encloses

$$\|Bf-w\|_{L^2(\nu)}<\frac9{8000}.$$

Its numerical upper bound is approximately $0.001123653$. This upper
enclosure does not reach $10^{-4}$; it is not a lower bound on the true
residual or on any achievable correction. The candidate's sampled
residual near $0.000456042$ is selection data, not this certificate.

The accepted inverse bound with $c_*=11/2500$ consequently gives, under
the same actual-model premises,

$$\|n_h-n\|\le\frac{45}{176},\qquad
\|C_\pm(n_h-n)\|\le\frac9{160\sqrt{11}}.$$

These are bounds for one fixed input and one common correction. They do
not bound the original half-slack, the regularization error on a required
input class, a cofinal comparison or the Robin/RH criterion.

The stronger [whole-space negative-edge block constant](theta-negative-block-gap.md)
$c_{**}=1/100$ improves this conversion, under its actual-model and
numerical-supplier premises, to

$$\|n_h-n\|<\frac9{80},\qquad
\|C_\pm(n_h-n)\|<\frac9{800}.$$

The same residual bound is reused; no midpoint action or residual
envelope is recomputed for this consequence. It still does not reach
the residual target $10^{-4}$.

## Support and retained action

For $u>0$, let $b(u)\in(0,1)$ be the unique positive root of

$$u(u+1)b^3+(3u^2+2u+1)b^2+2(u^2+1)b-2u=0.$$

All positive-degree coefficients are positive; the polynomial is
negative at zero and positive at one. The active signed bands start at
distances $d_+(r)=\log(1+b(e^r))$ and
$d_-(r)=\log(1+b(e^{-r}))$. The selected root is enclosed by a local
Rouche disk; no separation of the other cubic roots is required.

With $s=r+\varepsilon t$, $\varepsilon\in\{1,-1\}$, each band contributes

$$\int_{d_\varepsilon(r)}^\infty
\left[1-\frac{\psi_\Gamma(t)}{2\cosh(r/2)\cosh(s/2)}\right]
[f(r)\Phi(s)-\Phi(s)f(s)]\cosh(s/2)\,dt.$$

There is no additional factor: the $1/2$ in $B$ cancels the factor two
in $d\nu=2\Phi\cosh(x/2)dx$. Each integral is retained to $t=5$;
the left chart may be split at $t=r$. The bounded analytic expression
agrees with the positive-part kernel on the real active band. Invalid
theta charts, enclosed poles and nonfinite callback values are rejected.
Returned balls, rather than nominal quadrature tolerances, carry the error.

## Derivative and spatial allowances

For the inherited polynomials $P_{j,a}$, write $U=e^{2z}$ and

$$\Phi^{(j)}(z)=e^{5z/2-\pi U}D_j(z),$$

$$D_j=\sum_{n\ge1}
[4\pi^2n^4UP_{j,9/2}(\pi n^2U)-6\pi n^2P_{j,5/2}(\pi n^2U)]
e^{-\pi(n^2-1)U}.$$

Eight terms are retained. On each valid chart, let
$\lambda=\pi e^{2\inf\Re z}\cos(2\sup|\Im z|)>0$. Every omitted
monomial is bounded by

$$\sum_{n\ge9}n^p e^{-\lambda(n^2-1)}
\le\frac{9^p e^{-80\lambda}}{1-(10/9)^p e^{-19\lambda}}.$$

The denominator is checked strictly positive. Even jets through order
14 use reflection; odd jets through order 15 use the real overlap chart
$r>-1/8$. Ratios cancel the common small exponential factor before
division. Polynomial evaluation uses the existing FLINT composition
$P(z)=P(c+(z-c))$ at a point midpoint $c$; the underlying analytic
polynomial is unchanged. Absolute-coefficient series tails remain separate.

For $s\ge0$, the program also obtains finite constants $C_j$ with
$|\Phi^{(j)}(s)|\le C_j e^{(9/2+2j)s-\pi e^{2s}}$.
Define the inherited exponential-integral upper allowance

$$T_p(S)=\frac1{2\sqrt{e^{2S}}}
\int_{e^{2S}}^\infty y^p e^{-\pi y}\,dy.$$

It bounds $\int_S^\infty e^{(5+4k)s-\pi e^{2s}}ds$ with
$p=2+2k$. Also $s^2\le e^{2s}$ and $s^4\le e^{4s}$.
At each real retained row, $S=5-|r|$ pays both omitted signed bands by

$$2\left[|f(r)|C_0T_2+C_0T_3+
\sum_k|a_k|(C_{2k}T_{2+2k}+4^{-k}C_0T_2)\right].$$

The full $M_1\ge\|f\|_{L^1(\nu)}$ is bounded by interval upper sums
of $4|\Phi(r)f(r)|\cosh(r/2)$ on $[0,5/2]$ and four times the
corresponding weighted-source tail. Products $\Phi f$ are computed
directly; exterior growth of the source is included.

## From midpoint bounds to the whole norm

For a real cell let $g>0$ bound both active gaps below. On active edges,
$|\partial_ra|\le\coth(g)$; inactive edges have derivative zero almost
everywhere, and the boundary has zero edge weight. Probability
normalization and dominated local Lipschitz transport give

$$|(Bf)'|\le\tfrac12[|f'|+\coth(g)(|f|+M_1)].$$

Add the direct interval upper for $|w'|$. A certified midpoint residual
upper plus cell half-width times this derivative upper bounds the
residual over the entire cell. Its squared value times cell width and
the upper folded density $4\Phi(r)\cosh(r/2)$ is integrated over 512
cells. The source L1 upper uses 1024 cells.

For $r\ge R=5/2$, put $A=4\pi^2-6\pi>0$ and
$c=\sum|a_k|4^{-k}$. The first positive theta term gives

$$|f(r)|\le r^2+c+\sum_k|a_k|C_{2k}A^{-1}e^{4kr}.$$

Cauchy on its nine summands bounds the exterior source squared norm by

$$4C_0\,9\left[T_4+c^2T_2+
\sum_k(a_kC_{2k}/A)^2T_{2+4k}\right].$$

Finally $|Bf|\le(|f|+M_1)/2$ and
$|w|\le\sum|b_j|$ imply
$|Bf-w|^2\le3|f|^2/4+3M_1^2/4+3(\sum|b_j|)^2$.
The last two terms use exterior mass upper $4C_0T_2$. This bounds the
full physical exterior, rather than merely its small probability mass.
The squared exterior allowance is below $4.762\times10^{-139}$.

## Reuse and reproduction

The [midpoint input rows](theta-common-residual-rows.json) were acquired
by the pinned supplier commit recorded there. Their bounds include the
actual action quadrature, individual zero balls and full action tails.
The current norm calculation reuses those 512 values and executes no
action quadrature. Its input hashes and complete ordered grid are checked.
These structural checks do not prove arbitrary supplied row values;
certified midpoint bounds remain explicit premises of `--rows`.

From the repository root, with Python 3.13.12, python-flint 0.9.0 and
192-bit arithmetic:

```sh
uv run --no-project --python 3.13.12 --with python-flint==0.9.0 python docs/reports/theta-mixed-matrix/theta_common_residual_bounds.py --candidate docs/reports/theta-mixed-matrix/theta-common-residual-candidate.json --rows docs/reports/theta-mixed-matrix/theta-common-residual-rows.json --output /tmp/theta-common-residual-bounds.json
```

Omitting `--rows` acquires the midpoint actions afresh. It need not
reproduce identical enclosure widths. No producer for the older matrix,
FFT or derivative grids is executed: only the exact polynomial helper
definitions and numerical libraries are reused. Mathematical review
and publication checks concern this fixed candidate and interface;
they provide no model diversity or Lean/kernel certification.
