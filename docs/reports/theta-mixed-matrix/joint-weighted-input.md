# A directed weighted input from the saved joint high floor

The [complete joint high estimate](joint-high-floor.md) saves every
pointwise joint-floor lower bound before taking a scalar minimum. Keep
those bounds to supply a spatial inverse weight at the same $N=64$,
$c=3/8$ and actual minimal theta realization. The
[common-action coefficients](ground-residual.md) then pay a weighted
omitted-action input without another theta grid or source solve.
This is an application of existing form, inverse and action tools;
their original-model premises remain conditions, rather than facts
certified by parsing the saved JSON or by a new Lean proof.

Complex pairings and the common coefficient maps use the
[first-slot-linear matrix convention](README.md#complex-inner-products-for-matrix-reports).

## Keep the pointwise supplier before minimizing

Let $j_i$ be the exact saved lower endpoint for
$J_{32}=W+m(32)s^2$ on the $i$th absolute-value cell, and let
$j_{\rm ext}$ be the saved exterior lower endpoint. The cells cover
$[0,3/2]$ with adjacent endpoints $3i/256$.
Let $\ell$ be the saved upper bound for $m(32)\eta_{64}^2$.
Define the even step potential

$$
V_{\rm step}(x)=
\begin{cases}
j_i-c-\ell,& |x|\text{ belongs to cell }i,\\
j_{\rm ext}-c-\ell,& |x|>3/2.
\end{cases}
\tag{JW1}
$$

Common endpoints may be assigned either adjacent value; they have
zero measure. For every vector in the original high form domain, the
existing inequality before the scalar minimum gives

$$
C[q]\ge\int V_{\rm step}|q|^2dx
 +c|\langle v_0,q\rangle|^2.
\tag{JW2}
$$

All complete Gamma and prime-row terms are those of the joint supplier.
At $c=3/8$, every cell potential is positive. With $\delta_0$ the
saved high floor minus $3/8$, exact arithmetic gives
$V_{\rm step}\ge\delta_0>0$; the final directed scalar-floor rounding
can make this inequality strict in its last bits.
Consequently $w_{\rm step}=V_{\rm step}^{-1}$ is bounded positive
and $w_{\rm step}\le\delta_0^{-1}$. This is a direct high-form input
at the old band, not an assertion that $64\ge N_w(1/8)$ in (WH1).

Reuse the bounded positive shorting/rank-one tools in
[WH6--WH8](../../../Library/Weil/fukushima2011dirichlet.md#keep-the-high-constraint-and-the-exact-ground-term)
with this new $V,w$. Their common dual-source construction in
[SC19--SC22](sharp-center.md#pay-weighted-action-errors-with-one-common-dual-source)
needs bounded positive multiplication, not a smooth weight. The actual
operator, high domain and exact ground term are those of (JW2).

## A paid weighted output cap

Let $u_i$ be each saved upper endpoint for $s^2$ on the same cell.
Use $b=3/8$ and the existing
[WC2 envelope](../../../Library/Analytic/romik2021orthogonal.md#weighted-fourier-coefficient-suppliers),
$|s(x)|\le K_0\exp(-b e^{2|x|})$. A sufficient squared cap is

$$
\kappa_{\rm step}^2\ge
\max\left\{
\max_i\frac{u_i}{j_i-c-\ell},\quad
\frac{K_0^2e^{-2b e^3}}{j_{\rm ext}-c-\ell}
\right\}.
\tag{JW3}
$$

Thus $\sqrt{w_{\rm step}}s\le\kappa_{\rm step}$ everywhere except
irrelevant cell endpoints. The existing positive Gamma tail gives
$\kappa_{\rm step}\sigma_J\|(su)''\|_2$ for its weighted action,
where $\sigma_J=1/[2(2J-3/2)^2]$ and $su\in H^2$.
The complete omitted-prime action costs
$\delta_0^{-1/2}E_{{\rm p},64}\|u\|_2$; the inherited
$E_{{\rm p},64}$ pays every omitted prime power and both adjoints.
No weight is moved through $Q$.

## The same common ground complement and old action cutoffs

Keep exactly the [HT2 correction](high-trials.md#exact-ground-lift)
and its fixed $Z=QH_{1024,64}EB$. For
$p_\perp=(I-\Pi_0)p$, set $q_\perp=ZA E^*p_\perp$.
The inherited $A_{64},F_A,U,R$ supply

$$
\|(sp_\perp)''\|_2\le A_{64}\|p_\perp\|_2,\quad
\|(sq_\perp)''\|_2\le F_AU\|p_\perp\|_2,\quad
\|q_\perp\|_2\le F_AR\|p_\perp\|_2.
$$

Here $U,R$ are the existing common five-generator upper bounds;
restricting them to the four $Z$ columns does not select new optimizers.
Use the old action counts $J_\ell=1024$, $J_h=262144$ and $L=64$.
With $\alpha=1/8$, the actual and retained dual sources are

$$
\begin{aligned}
a&=H_c(p_\perp-q_\perp)-\alpha q_\perp,\\
a_{\rm ret}&=H_{c,J_\ell,64}p_\perp
 -H_{c,J_h,64}q_\perp-\alpha q_\perp.
\end{aligned}
\tag{JW4}
$$

Multiplication and the exact mean remain in both actions. Separate
action cutoffs do not redefine $Z$ or change the common coefficient map.
The two existing action bounds now give

$$
\begin{aligned}
\|\sqrt{w_{\rm step}}(a-a_{\rm ret})\|_2
&\le E_{\rm step}\|p_\perp\|_2,\\
E_{\rm step}&=\kappa_{\rm step}
 (\sigma_{J_\ell}A_{64}+F_A\sigma_{J_h}U)
 +\delta_0^{-1/2}E_{{\rm p},64}(1+F_AR).
\end{aligned}
\tag{JW5}
$$

This is uniform on the entire low band through the same fixed $Y$.
For the exact ground column $p_\perp=q_\perp=0$, so the omitted-action
error vanishes. In (SC22) it supplies the error form
$E_{\rm step}^2\|(I-\Pi_0)p\|_2^2$ while preserving the ground row
and its nonzero trial contribution. The compared scalar-transfer budget
uses the identical inputs and counts, replacing only $\kappa_{\rm step}$
by $\delta_0^{-1/2}S_0$.

## Directed result and remaining scope

The [coefficient-only program](joint_weighted_input.py) reads six existing
result files, records their hashes, verifies their linked provenance and
parameter agreement, and writes [exact weights and new input bounds](joint-weighted-input-result.json).
It computes rational cell transforms and 128-bit ball coefficients;
it executes zero theta callbacks and no old producer, trial selection,
derivative grid, action acquisition or numerical matrix solve.
Rounded outward at the existing $c=3/8,N=64$:

| Input or comparison | Upper bound |
|---|---:|
| Weighted output cap $\kappa_{\rm step}$ | $0.8108311869462900$ |
| Same scalar output cap $\delta_0^{-1/2}S_0$ | $4.019065358030263$ |
| Common weighted action error $E_{\rm step}$ | $0.000681201904155447$ |
| Same-input scalar-transfer action budget | $0.003376528947525323$ |
| Weighted/scalar common-budget ratio | $0.201746205864666$ |

These are upper-budget comparisons, not measured residual norms or
inverse-coupling gains. The chosen low dual trial may still cost more
than the old minimizing allowance. Weighted retained-action and source
Grams remain unevaluated. A discontinuous step weight cannot be inserted
into the old global holomorphic trapezoid estimates without paying its
cellwise integration and boundary errors.

The program also accepts a rational $c$ for which the saved high floors
leave positive potentials. Old retained-action tables remain specific to
$c=3/8$; other parameters receive only an analytic weight and tail-input
supplier, not those action or Gram entries. This fixed high supplier does
not cover a cofinal $c\uparrow1/2$ sequence. The saved conditional
$0.4605$ global lower comparison is not recomputed or replaced.
Original common cofinal low/complementary-low signs, the endpoint
half-bound, RH, full Robin and Lean certification remain unresolved.

From the repository root:

```sh
uv run --no-project --python 3.13.12 --with python-flint==0.9.0 python docs/reports/theta-mixed-matrix/joint_weighted_input.py
```

`--input-dir`, `--output` and rational `--c` are explicit optional inputs.
The program is project-authored; python-flint/FLINT supplies directed
arithmetic and its dependency licensing. Successful parameter/provenance
checks do not establish the external mathematical premises of the data.

The [paid finite-core residual correction](weighted-residual-core.md)
uses this same step potential with the separately saved full-Gamma
residual source and its whole-line Gram. Its local polynomial integration
pays the step boundaries without reusing a global holomorphic trapezoid
bound. This supplies a common residual gain input, while JW4's different
finite-$J$ dual-action/source Grams and common cofinal signs remain open.
