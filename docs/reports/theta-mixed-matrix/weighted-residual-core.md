# A paid common residual correction on the finite theta core

This conditional paper input reuses the saved
[full-Gamma low actions](low-common-action.md),
[full-Gamma high actions](high-full-action.md),
[common whole-line residual Gram](restricted-schur.md) and
[pointwise joint high weight](joint-weighted-input.md).
It integrates only the new finite-core correction from existing samples.
Cauchy estimates, polynomial interpolation and exact polynomial integration
are classical tools. Their use here is a model-specific numerical input,
not a new generic theorem or a Lean certificate.
The divided-difference averaging and Lagrange remainder are reused from
Carl de Boor, [*Divided Differences*](https://arxiv.org/abs/math/0502036v1),
*Surveys in Approximation Theory* **1** (2005), 46–69: Section 9,
printed page 62, equations (47)–(48), and printed page 64, equation (52)
and the adjacent Lagrange error formula.

## Keep the actual common residual

Use $N=64$, $c=3/8$, $\alpha=1/8$, the same $95$-column isometry $E$,
the fixed $Z=QH_{1024,64}EB$, and the saved exact dyadic $4$-by-$95$
matrix $A$. The retained action has full Gamma and all prime powers
through $64$. Write

$$
R_{64}=QH_L-(\alpha Z+QH_Z)A
=QT_{\infty,64}(E-ZA).
\tag{WR1}
$$

The saved matrix $G_{64}=R_{64}^*R_{64}$ and bound
$\|R_{64}\|\le\rho<0.00805805$ are reused directly.
For the full-prime source $R$, the same joint prime transport gives
$\|R-R_{64}\|\le\varepsilon_R<1.147\cdot10^{-18}$.
All maps and products use one common coefficient vector.

The exact saved Householder frame $V$ is an isometry onto
$e^\perp$, where $e=E^*Pv_0$. On this frame the true HT2 lift is
$ZAV$. The raw $95$-column source is not asserted to vanish at $e$.
The known exact ground source may be adjoined separately with zero
error row and column. Pairings and matrix entries follow the
[first-slot-linear convention](README.md#complex-inner-products-for-matrix-reports).

## Subtract a nonnegative core contribution

Take the safe scalar floor
$\delta_0=0.0383682545007734$ from the existing residual comparison,
$w_0=\delta_0^{-1}$, and the saved even step weight $w=V_{\rm step}^{-1}$.
Every cell and exterior potential is checked to be at least $\delta_0$.
Thus $0<w\le w_0$. On positive cell $i$, let
$\beta_i=w_0-w_i\ge0$, and write $B=\max_i\beta_i$.

The existing bounded high inverse comparison, conservatively dropping
the favorable ground term, gives

$$
\langle r,C^{-1}r\rangle
\le\int w|r|^2
\le w_0\|r\|^2-\int_{|x|\le3/2}(w_0-w)|r|^2.
\tag{WR2}
$$

The omitted exterior correction is nonnegative. No weight is moved
through $Q$, and the sharp projected residual is not called localized.
The full-line scalar Gram has already been paid; only the subtracted
core Gram needs new integration. This uses the existing full-Gamma
samples, rather than substituting them for JW4's finite-$J$ action.
The selected low dual lift and its possible excess cost are not needed.

## Interpolate only existing sample rows

The saved even sources have spacing $h=1/256$ and cover $|x|\le4$.
Positive cell $i$ is $[3ih,(3i+3)h]$. Use its $64$ existing nodes
$k=3i-30,\ldots,3i+33$, with negative rows supplied by evenness.
Only absolute indices $0,\ldots,414$ are used.

Set $t=(x-3ih)/h\in[0,3]$, and let $\ell_j(t)$ be the cardinal
polynomials of degree $63$ on nodes $-30,\ldots,33$.
Their common exact rational kernel is

$$
K_{jk}=\int_0^3\ell_j(t)\ell_k(t)\,dt.
\tag{WR3}
$$

Choose exact midpoints of the saved dyadic source intervals, forming
one common sample matrix $M_i$. This choice approximates the original
vectors; it does not redefine them. The polynomial core Gram is

$$
D_{\rm poly}=2h\sum_{i=0}^{127}\beta_i M_i^*KM_i.
\tag{WR4}
$$

All cross entries remain present. The factor $2$ accounts for the
negative half-line, and $h$ transports the exact polynomial integral
back to the physical coordinate.

## Pay continuum and sample errors jointly

Reuse the actual strip-line $L^2$ caps $D_l,D_h,U_h$ for $H_L,H_Z,Z$
and the saved $F_A\ge\|A\|$. Sharp projection is contractive on the
same weighted Fourier lines. At $\delta=1/8$, a common cap is

$$
D_{\rm line}=D_l+F_A(D_h+\alpha U_h).
$$

The wider OA7 cap for $Z$ remains a cap on the narrower lines:
even Fourier data make the corresponding $\cosh$ weight monotone.
The existing strip Fourier representation and Cauchy--Schwarz give,
uniformly on the common coefficient unit ball,

$$
|R_{64}(x+iy)u|
\le\frac{D_{\rm line}}{\sqrt{\pi(\delta-|y|)}}.
$$

Use circle radius $s=3/25<\delta$. Cauchy's derivative estimate and
the real-node divided-difference averaging formula give the interpolation
cap

$$
\varepsilon_{\rm an}
=\frac{D_{\rm line}}{\sqrt{\pi(\delta-s)}}
 \left(\frac hs\right)^{64}
 \prod_{j=2}^{31}(j+1/2)^2.
\tag{WR5}
$$

The remainder bound applies also to complex coefficient vectors;
it uses derivative averaging, not a single real mean-value point.
To verify the nodal product bound, put $y=t-3/2$. For $y^2\in[0,9/4]$,
$|(y^2-1/4)(y^2-9/4)|\le1$; each remaining paired factor is bounded
by $(j+1/2)^2$.

At each saved node, bound the low row error by the Euclidean norm of
its $95$ component half-widths. The $Z$ and $QH_Z$ errors use their
$4$ component half-width norms. This supplies one row-operator cap

$$
\varepsilon_s
\ge\max_k\{e_l(k)+F_A[\alpha e_Z(k)+e_h(k)]\}.
$$

Express each $\ell_j(3u)$ in the degree-$63$ Bernstein basis on
$u\in[0,1]$, with exact coefficients $b_{jk}$. The sufficient
Lebesgue cap $\Lambda=\sum_j\max_k|b_{jk}|$ gives the common point error
$\varepsilon=\varepsilon_{\rm an}+\Lambda\varepsilon_s$.
No independence of source errors is assumed.

Let $D_{64}$ denote the actual retained-source core Gram.
Using the same whole-line $\rho$ bound and the core length $3$ gives

$$
\|D_{64}-D_{\rm poly}\|
\le\eta_{\rm int}
:=B(2\rho\sqrt3\,\varepsilon+3\varepsilon^2).
\tag{WR6}
$$

For the full-prime core Gram $D$, the same joint omission error gives

$$
\|D-D_{64}\|\le\eta_p
:=B(2\rho\varepsilon_R+\varepsilon_R^2).
\tag{WR7}
$$

These are operator bounds on the shared coefficient space. The
integration error uses the true retained source norm, not an
independently chosen polynomial or trial optimum.

## Transport the exact frame and retain the comparison gain

Apply the saved exact ground frame, including all component uncertainty:

$$
G_{\rm gain}=V^*D_{\rm poly}V-(\eta_{\rm int}+\eta_p)I_{94},
\qquad V^*DV\succeq G_{\rm gain}.
\tag{WR8}
$$

The numerical implementation subtracts a fixed outward dyadic cap
for $\eta_{\rm int}+\eta_p$, including the rounding of both components.
The full-prime scalar baseline is still

$$
U_{\rm scalar}^{\rm paid}
=w_0\bigl[V^*G_{64}V+(2\rho\varepsilon_R+\varepsilon_R^2)I_{94}\bigr].
$$

An upper inverse allowance is $U_{\rm scalar}^{\rm paid}-G_{\rm gain}$.
The core prime error does not replace the baseline prime allowance.
When inserted into the RS8 Schur comparison, the existing trial-form
prime error also remains; only this common core correction is added.

The existing scalar residual allowance can therefore be reduced by
this enclosed Hermitian gain matrix. The output entry intervals enclose
one common Hermitian matrix; taking each entry's lower endpoint does not
give a Loewner lower matrix. Its positive semidefiniteness is
not assumed or certified. Although the true core contribution $D$ is
nonnegative, subtracting a uniform error can leave negative directions
in its computable minorant. A positive diagonal or trace does not prove
positivity on all coefficient directions.

The [directed result](weighted-residual-core-result.json), produced by
[the coefficient-only program](weighted_residual_core.py), has these
rounded outward bounds under the inherited mathematical suppliers:

| Quantity | Bound |
|---|---|
| Analytic interpolation point error | $<8.222398\cdot10^{-15}$ |
| Bernstein Lebesgue cap | $<4.957270$ |
| Common total point error | $<1.313885\cdot10^{-7}$ |
| Core integration and input error | $<9.069831\cdot10^{-8}$ |
| Full-prime core error | $<4.569868\cdot10^{-19}$ |
| Restricted gain trace | $>0.00085514405219450$ |
| Gain on frame column indexed $2$ from zero | $>0.00020422788316278$ |

The last entry reduces the same scalar residual upper allowance on
that exact normalized frame direction. It is not a change in the true
inverse quadratic value, a uniform percentage saving, or a new matrix
sign. The program retains all $94^2$ gain entries. It performs no
theta callback, old action acquisition, coefficient solve or old LDL
replay. The conditional global $0.4605$ comparison is unchanged.

This fixed-family input does not provide the complementary low-band
estimate on a common cofinal family. The original all-input half-bound,
cofinal low/complementary-low signs, RH, full Robin and Lean certification
remain unresolved. Input hashes and parameter guards identify the
saved realization; they do not prove its original-model premises.

From the repository root:

```sh
uv run --no-project --python 3.13.12 --with python-flint==0.9.0 python docs/reports/theta-mixed-matrix/weighted_residual_core.py
```

`--input-dir` and `--output` select explicit data and destination paths.
The program is project-authored; python-flint/FLINT supplies exact
rational polynomial operations and directed arithmetic with its
dependency licensing.

The [continuous-sinc reconstruction](sinc-weighted-residual-core.md)
reuses this integration and exact-frame machinery with the already saved
unprojected rows. It pays reconstruction/source arithmetic separately
and uses the actual core weight mass. Its smaller error cap and named
direction comparison do not assert a uniform matrix gain or new sign.
