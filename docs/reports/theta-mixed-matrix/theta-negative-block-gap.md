# Whole-space negative-edge gap from the existing FIB partition

This is a conditional paper estimate and directed numerical experiment
for the [actual bounded negative-edge operator](../../../Library/Weil/lagarias2004li.md#even-geometry-gives-a-stronger-negative-edge-inverse-constant).
It reuses the existing five-mode interval tiling, theta series supplier,
[validated ball integration](../../../Library/Analytic/johansson2018ballintegration.md),
conditional variance decomposition, Cholesky preconditioning and
Gershgorin's theorem. No new generic theorem or arithmetic advantage of
the FIB labels is claimed. These labels index a partition of the same
radial theta probability space; their interval lengths are not its
probability weights.

Under the inherited actual-model and numerical-supplier premises, the
[directed result](theta-negative-block-gap-result.json) gives

$$
\|C_-h\|^2\ge\frac1{100}\operatorname{Var}_\nu(h)
\qquad(h\in L^2_{\rm even}(\nu)). \tag{NB1}
$$

This improves the previous $11/2500$ lower constant for $B=C_-^*C_-$.
It does not bound the original energy $D$ or its half-slack and does not
settle the cofinal projected comparison, Robin or RH. No Lean/kernel
certification of this new numerical/model interface is asserted.

## Complete partition and actual masses

Write $h(x)=f(|x|)$, and let $\mu$ be the distribution of $|X|$ for
$X\sim\nu$. The accepted even normalization is

$$
d\mu(r)=4\Phi(r)\cosh(r/2)\,dr,\qquad
\|C_-h\|^2=\frac18\iint k(r,s)|f(r)-f(s)|^2\,d\mu(r)d\mu(s),
$$

where $k(r,s)=a(r,s)+a(r,-s)$ and

$$
a(x,y)=\left[1-\frac{\psi_\Gamma(|x-y|)}
 {2\cosh(x/2)\cosh(y/2)}\right]_+,
\qquad \psi_\Gamma(t)=\frac{e^{-t/2}}{1-e^{-2t}}.
$$

The zero-distance value is taken to be zero. It is consistent with the
limit of this positive-part conductance and has no effect on the integral.

Reuse the [legal FIB tiling](../../../Library/Weil/jarohsweth2020local.md#reuse-the-existing-fib-five-mode-interval-partition)
with $\phi=(1+\sqrt5)/2$, $\lambda=3-2\phi$,
$K_0=[-1,\phi]$ and $K_1=[-1,\phi-1]$.
The increments in $\mathbb Q[\phi]$ for
`[null,2,3,2 5,5]` are $0,1,1-\phi,3-\phi,2-\phi$.
The allowed successors are
$0\to0:\mathrm{null},2,3$; $0\to1:25,5$;
$1\to0:\mathrm{null},3$; $1\to1:5$.
Their depth-two cylinders give 21 intervals. The affine observation

$$
r=\frac32(2-\phi)(y+1)
$$

sends them to a partition of $[0,3/2]$. Exact ring-coefficient equality
checks every seam and both outer endpoints; ball arithmetic checks
strictly positive widths. Endpoint assignments can be made half-open,
since $\mu$ is absolutely continuous.

Add the whole outside cell $[3/2,\infty)$, making 22 cells. For each
finite cell, the reused holomorphic theta supplier encloses the actual
mass by `acb.integral`. Its series tail remains included. Invalid
complex charts return nonfinite values, which the integration routine
rejects. Every accepted mass enclosure is finite and strictly positive.
The outside mass is enclosed by $1-\sum_{i<21}m_i$, using the inherited
exact probability normalization. Its enclosure is strictly positive,
approximately $5.446880442\times10^{-25}$. This subtraction accounts
for the whole exterior; it is not a finite cutoff or a tail discarded
because its mass is small.

## Block conductance minorants

For a cell $I_i$, let $l_i$ be a nonnegative directed lower bound on
its left endpoint. For $i\le j$, let $g_{ij}$ be a nonnegative directed
lower bound on the distance between the two whole cells. Adjacent,
overlapping and diagonal cells have $g_{ij}=0$; the outside cell uses
its finite left endpoint. Define

$$
\eta(t;l_i,l_j)=
\begin{cases}
\left[1-\dfrac{\psi_\Gamma(t)}
 {2\cosh(l_i/2)\cosh(l_j/2)}\right]_+,&t>0,\\
0,&t=0.
\end{cases}
$$

Because $\psi_\Gamma$ decreases and $\cosh$ increases on nonnegative
radials, $\eta(l_i+l_j;l_i,l_j)$ bounds the opposite-sign edge below,
and $\eta(g_{ij};l_i,l_j)$ bounds the same-sign edge below. The program
takes nonnegative dyadic lower points of their sum and sets them
symmetrically to obtain $0\le W_{ij}\le k(r,s)$ on $I_i\times I_j$.
Dropping an edge when this bound is zero is valid only in this lower
minorant. All masses, including the outside mass, remain in its rows.

## Within-cell fluctuations and block means

For each actual $m_i=\mu(I_i)>0$, let $f_i$ be the conditional mean of
$f$ on $I_i$ and $v_i$ its conditional variance. Put

$$
d_i=\frac14\sum_jW_{ij}m_j,\qquad
u_i=\sqrt{m_i},\qquad z_i=\sqrt{m_i}f_i,
$$

$$
L=\operatorname{diag}(d_i)-\frac14
 (W_{ij}\sqrt{m_im_j})_{ij}.
$$

The standard product-measure variance expansion gives

$$
\begin{aligned}
\|C_-h\|^2&\ge\sum_i m_i d_i v_i+z^*Lz,\\
\operatorname{Var}_\mu(f)&=\sum_i m_i v_i+
 \|z\|^2-|u^*z|^2.
\end{aligned} \tag{NB2}
$$

In particular the outside cell retains its own conditional variance.
This step controls all ambient $L^2$ inputs, including fluctuations
invisible to the finite block means. No constant-on-cells assumption
or finite-dimensional exhaustion argument is made.

Actual probability normalization gives $\|u\|=1$ and $Lu=0$. For
$c=1/100$, it is sufficient to certify

$$
\min_i d_i\ge c,\qquad A=L-cI+uu^*\succeq0. \tag{NB3}
$$

The second condition gives $L\ge c$ on $u^\perp$; (NB2) then yields
(NB1). Ball mass enclosures need not independently sum to exactly one;
they enclose the same actual normalized vector, to which this argument
applies.

## Directed finite matrix certificate

NumPy Cholesky of the midpoint of $A$ selects a lower triangular
preconditioner $P$. Every selected floating entry is converted to its
exact dyadic rational, and every diagonal is checked positive. NumPy
eigenvalues are retained only as explicitly uncertified diagnostics.
No midpoint sign is used for acceptance.

The validated default `arb_mat.solve` encloses $P^{-1}$. Directed ball
matrix products enclose $R=P^{-1}AP^{-T}$. For every row, the program
requires a strictly positive lower bound on

$$
R_{ii}-\sum_{j\ne i}|R_{ij}|.
$$

For the actual real symmetric congruence, Gershgorin then gives positive
definiteness. Since $P$ is invertible, $A$ is positive definite too.
The [result](theta-negative-block-gap-result.json) records exact dyadic
mass endpoints, all lower conductances, the point preconditioner and
all congruence margins. The minimum within-cell degree exceeds
$0.01126121106468$ and the minimum congruence margin exceeds
$0.99999999999997$. The outside degree exceeds $0.40082234517683$.
Both sufficient conditions at $1/100$ pass.

## Consequence for the existing common correction

The accepted critical compression $G=P_NB|_N$ therefore obeys, under
the same premises,

$$
\|G^{-1}\|\le100,\qquad \kappa(G)\le50,\qquad
\|I_N-2G\|\le49/50.
$$

For the existing fixed quadratic candidate, reuse its
[whole-space residual bound](theta-common-residual-bounds.md)
$\|B(h-n)-w\|<9/8000$, with $n\in N$ and $w\in N^\perp$.
No action rows or residual envelopes are recomputed. Projection of
this residual gives $G(n_h-n)$; the accepted common Gram identity gives

$$
\|n_h-n\|<\frac9{80},\qquad
\|C_\pm(n_h-n)\|<\frac9{800}.
$$

These improve error conversion for that one common source. They do not
improve its residual certificate to $10^{-4}$ or supply an original
form-domain assertion for $x^2$.

## Reproduction

From the repository root:

```sh
uv run --no-project --python 3.13.12 --with python-flint==0.9.0 --with numpy==2.5.3 python docs/reports/theta-mixed-matrix/theta_negative_block_gap.py --depth 2 --target 1/100 --output /tmp/theta-negative-block-gap-result.json
```

The producer records its own hash, both reused supplier hashes and
runtime versions. Returned enclosures carry numerical evidence under
those suppliers' contracts; structural data or a successful numerical
run alone does not provide Lean certification or discharge the
unresolved Robin/RH estimates.
