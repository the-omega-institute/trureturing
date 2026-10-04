# Directed weighted Fourier deficit

The [weighted Fourier construction](../../../Library/Weil/fukushima2011dirichlet.md)
uses a scalar deficit to select a sufficient high-frequency gap. This
program encloses that deficit for the actual even theta model at
$\varepsilon=1/4$. It reuses the canonical `phi` and `realphi` callback
functions from [scalar_pilot.py](scalar_pilot.py), including their
directed six-term theta remainder. It does not implement a second theta
kernel.

## Exact target and retained row

With $s^2=\Phi/(2\cosh(x/2))$ and
$c_\Gamma=\operatorname{digamma}(1/4)-\log\pi$, put

$$
R_B(x)=\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}
s(x)(s(x+\log n)+s(x-\log n)),\qquad
W(x)=\tfrac12+c_\Gamma s(x)^2-R_B(x).
$$

The target is

$$
\mu_{1/4}=\sup_{x\in\mathbb R}
\frac{(3/8-W(x))_+}{s(x)^2}
=\sup_x\frac{(-c_\Gamma s(x)^2+R_B(x)-1/8)_+}{s(x)^2}.
$$

The program uses
$-c_\Gamma=\gamma+\pi/2+3\log2+\log\pi$.
All 27 prime powers through 64 occur, each with weight
$\log p/\sqrt{p^k}$ and both translated row directions.
The retained interval $[0,3/2]$ is covered by 1536 closed dyadic
boxes of width $1/1024$; evenness covers its reflection.

Cell upper bounds take upper numerator bounds and positive lower
denominator bounds. For shifted theta square roots, the theta upper
endpoint and denominator lower endpoint give a directed upper bound
even when a wide theta ball has an inconclusive lower endpoint. Principal
denominators and midpoint lower witnesses require certified positivity.
The lower witnesses omit only nonnegative row terms. Nonfinite values,
uncertified positivity, or ambiguous comparisons reject the computation.

## Complete omitted-row and exterior bounds

For $x\in[0,R]$, $R=3/2$, and $n>64$, the original-series tail and
$\|s\|_\infty^2\le9/5$ give, in each direction,

$$
s(x)s(x\pm\log n)\le K e^{-\alpha n^2},\qquad
K=\sqrt{72/5}\sqrt{9/5},\quad \alpha=\tfrac34e^{-3}.
$$

Here $\log64>R$ and $2\alpha64^2>1$ are certified. Using
$\Lambda(n)/\sqrt n\le n$ and the decreasing Gaussian integrand,

$$
R_{B,>64}(x)\le2K\sum_{n>64}ne^{-\alpha n^2}
\le\frac K\alpha e^{-\alpha64^2}.
$$

This upper bound includes both omitted directions and every omitted
prime power. It is below $5.141508540252718\cdot10^{-65}$.

The coefficient-row estimate underlying (BT), together with (JL) in the
[same-form exterior analysis](../../../Library/Weil/lenz2010compactness.md),
gives $W\ge1/2-d_R$ outside $[-R,R]$, with
$d_R\le160e^{-(3/8)e^{2R}}$.
At $R=3/2$ its directed upper endpoint is less than
$0.08569999335112469<1/8$. Thus the exterior deficit is zero; the
interval cover and row tail control the full real-line supremum.

## Result and scope

The [saved result](deficit-result.json) contains exact dyadic endpoints.
Rounded outward, they give

$$
\boxed{5.1451611371534522\le\mu_{1/4}
\le5.2350558731050110.}
$$

The width is less than the declared $0.1$ target. Of the 1536 boxes,
970 have certified nonpositive deficit numerator. The largest upper
cell is $[0,1/1024]$. The computation makes 168,960 theta calls.

This encloses only the scalar deficit in (WF4). The derivative norm,
commutator constants, full trial matrix signs, conditioning, and cofinal
window control remain separate obligations. A small deficit does not by
itself certify a sufficient bandwidth, the critical-half inequality,
RH or Robin. No new Lean certification is claimed.

## Reproduce

The recorded runtime is Python 3.13.12, python-flint 0.9.0, with 128-bit
ball arithmetic. From the repository root run

```sh
uv run --no-project --python 3.13.12 --with python-flint==0.9.0 python docs/reports/theta-mixed-matrix/deficit_profile.py
```

The command writes `deficit-result.json` beside the program. The callback
source hash records which canonical bytes supplied the theta values;
it is provenance, not a program-byte cache-reuse condition. Independent
checking reproduced the extremal endpoints and tail constants on small
inputs and checked the lower witness against a twelve-term original
series at 256-bit precision. The complete grid was not repeated for that
check. This project-authored program uses existing FLINT arithmetic;
dependency licensing is supplied by python-flint/FLINT.
