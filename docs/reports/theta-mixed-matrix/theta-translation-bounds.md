# Actual theta translation norms for fixed-parameter approximation

The [theta-translation Fredholm interface](../../../Library/Dynamics/clason2021regularization.md)
requires numerical bounds for $M_F\ge\|F\|$ and
$L_w\ge\sup_{|t|\le r}\|w'_t\|_\nu$. This computation supplies those
two inputs for $r=1/16$, with the original probability measure
$d\nu=2\Phi(x)\cosh(x/2)dx$. It uses the accepted theta representation
and derivative enclosures; it does not solve the Fredholm equation.

## Uniform interior bound

For the actual even translation vector,

$$w'_t(x)=\frac{\Phi'(x+t)-\Phi'(x-t)}{2\Phi(x)}
-\frac12\sinh(t/2).$$

The fundamental theorem of calculus and evenness of $\Phi''$ give,
uniformly for $|t|\le r$,

$$|w'_t(x)|\le\frac{r}{\Phi(x)}
\sup_{|s|\le r}|\Phi''(x+s)|+k,\qquad k=\tfrac12\sinh(r/2).$$

The [program](theta_translation_bounds.py) reuses only `polys`,
`scalar_constant` and `phi_derivatives` from the existing
[original derivative supplier](derivative_bandwidth.py). It imports their
definitions through the established AST extraction interface and records
the source hash. The old derivative grid and bandwidth computation are
not executed.

There are 2048 exact radial cells on $[0,2]$. Each cell's shifted range is
folded to $[\max(0,x_{\rm left}-r),x_{\rm right}+r]$ and covered by eight
initial subcells. A subcell is bisected when the supplier cannot certify
its positive denominator; recursion terminates only with certified
subcells or an error. The actual run has 18,380 accepted shifted leaves.
The maximum of their second-derivative bounds encloses the whole shifted
range. Integrating the squared displayed bound with the folded density
$4\Phi(x)\cosh(x/2)$ gives an upper bound for every $\|w'_t\|_\nu^2$
on the retained interval. All omitted theta indices are included in the
inherited six-term derivative remainder.

## Full spatial tails

Use the existing WC1 constants $C_0,C_2$ from the
[theta derivative note](../../../Library/Analytic/romik2021orthogonal.md).
For $x\ge2$, the first positive theta summand and WC1 give

$$\begin{aligned}
\Phi(x)&\ge c_0e^{9x/2-\pi e^{2x}},\qquad c_0=4\pi^2-6\pi>0,\\
\Phi(x)&\le C_0e^{9x/2-\pi e^{2x}},\\
\sup_{|s|\le r}|\Phi''(x+s)|
&\le C_2e^{17(x+r)/2-\pi e^{2(x-r)}}.
\end{aligned}$$

Let $U=e^4$ and $a=\pi(2e^{-2r}-1)>0$. The ratio in the interior
bound is at most

$$\frac{C_2e^{17r/2}}{c_0}
e^{4x+\pi(1-e^{-2r})e^{2x}}.$$

Square using $(p+q)^2\le2p^2+2q^2$ and bound the folded original
density by $4C_0e^{5x-\pi e^{2x}}$. The two tail contributions are
bounded by

$$\frac{8C_0r^2C_2^2e^{17r}}{c_0^2}J_6(a,U),
\qquad 8C_0k^2J_2(\pi,U),$$

where

$$J_m(b,U)=\frac{e^{-bU}}{2\sqrt U}
\sum_{j=0}^m\frac{m!}{j!}\frac{U^j}{b^{m-j+1}}.$$

This is the elementary integer exponential integral after
$y=e^{2x}$, enlarged by $y^{11/2}\le y^6/\sqrt U$ and
$y^{3/2}\le y^2/\sqrt U$ for $y\ge U$. Both spatial signs are
already included in the folded density. The larger tail contribution is
below $4.667\cdot10^{-43}$; neither tail is dropped.

## Inputs obtained and their scope

The [saved exact dyadic endpoints](theta-translation-bounds-result.json)
give $L_w<4.497207<9/2$. Since $w_0=0$,

$$\|F\|^2\le\|F\|_{\rm HS}^2
=\int_{-r}^r\|w_t\|_\nu^2dt
\le\frac{2r^3}{3}L_w^2.$$

Thus one may take $M_F=3/50$. For $m$ equal midpoint cells, the accepted
midpoint estimate gives

$$\delta_m=\|F-F_m\|
\le\frac{L_w}{m}\sqrt{\frac{2r^3}{3}}
\le\frac{3}{50m}.$$

R6 consequently bounds the same-source paired-edge discretization error
by

$$\|C_\pm(n_\varepsilon-n_{\varepsilon,m})\|
\le\frac{9}{5000\sqrt2\,\varepsilon}
\left(\frac2m+\frac1{m^2}\right)\|h-\nu(h)1\|_\nu.$$

For $\varepsilon=1/100$ and $m=256$, the coefficient is below $1/1000$.
This is a uniform fixed-parameter discretization bound. It supplies no
bound for the separate regularization error, no computed Fredholm matrix,
no whole-space complementary residual and no projected transfer sign.
The original half-bound, Robin and RH remain unresolved; there is no new
Lean certification or originality claim.

## Reproduce

The recorded runtime is Python 3.13.12, python-flint 0.9.0 and 192-bit
ball arithmetic. From the repository root:

```sh
uv run --no-project --python 3.13.12 --with python-flint==0.9.0 python docs/reports/theta-mixed-matrix/theta_translation_bounds.py --output /tmp/theta-translation-bounds.json
```

The command uses the canonical sibling supplier and writes only the
explicit output path. `--canonical` selects another supplier directory;
`--precision` requires at least 128 bits and `--boxes` at least 128 radial
cells. Alternate meshes can give wider bounds; the displayed rational
values refer to the saved 2048-cell run. The producer rejects a failed
denominator certificate after bounded subdivision, nonfinite output, a
missing supplier definition or an unproved positive tail rate.
The producer is project-authored; dependency licensing is supplied by
python-flint/FLINT.
