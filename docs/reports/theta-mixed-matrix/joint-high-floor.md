# A complete high-frequency block above the matrix threshold

At $N=64$, the [direct bandwidth supplier](derivative-bandwidth.md)
gives a sufficient high-frequency lower bound $5/16$. That bound is
below the fixed-window matrix threshold $c=3/8$. The present joint
estimate supplies a stronger complete high-frequency bound using the
same original theta coefficients and full symmetric prime row.

## Joint scalar lower bound

Use (WF1)–(WF5) from the
[actual even minimal realization](../../../Library/Weil/fukushima2011dirichlet.md).
Keep $s^2=\Phi/(2\cosh(x/2))$, the complete $B$ and

$$
R_B(x)=\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}
s(x)(s(x+\log n)+s(x-\log n)),\qquad
W(x)=\tfrac12+c_\Gamma s(x)^2-R_B(x).
$$

For the symbol and derivative bounds in the linked supplier define

$$
J_{32}(x)=W(x)+m(32)s(x)^2
=\tfrac12+(m(32)-|c_\Gamma|)s(x)^2-R_B(x).
$$

The certified lower endpoint of $m(32)-|c_\Gamma|$ is positive,
approximately $1.6276960243$. On each cell, multiply it by the lower
endpoint of $s^2$, subtract the complete retained row upper endpoint,
and subtract the analytic omitted-row upper bound. These directions
give a lower bound for $J_{32}$.

The program loads the canonical [deficit setup](deficit_profile.py) by
its AST prefix and stops before that program's grid. The imported setup
makes zero theta calls; the earlier deficit grid is not executed.
All 27 prime powers through 64 occur with both shifts, and the analytic
row tail includes every omitted prime power and both directions.
The new 128 closed dyadic boxes cover $[0,3/2]$. Their full intervals
give a lower bound for the joint scalar floor, rather than point samples
or a postprocessing of the earlier deficit supremum.

Reflection covers the negative half. Outside $[-3/2,3/2]$, the existing
coefficient-row and theta estimates give
$W\ge1/2-d_{3/2}$, with
$d_{3/2}\le160e^{-(3/8)e^3}$. Since $m(32)s^2\ge0$,
this is also a lower bound for $J_{32}$ there.
The [saved result](joint-high-floor-result.json) retains every cell's
coefficient endpoints and joint floor for reuse. Rounded downward,

| Region | Lower bound for $J_{32}$ |
|---|---:|
| $|x|\le3/2$ | $0.4675789218114477$ |
| $|x|>3/2$ | $0.4143000066488753$ |
| Whole real line | $0.4143000066488753$ |

## Complete form and variance gap

For every even $v$ in the actual minimal form domain with
$\widehat v=0$ on $|\xi|<64$, (WF5) and the complete row comparison
give

$$
\widetilde D(v)\ge\int J_{32}(x)|v(x)|^2dx
-m(32)\eta_{64}^2\|v\|_2^2.
$$

The independently supplied leakage upper bound is
$m(32)\eta_{64}^2<0.0009317521481018941$. The exact saved endpoints
therefore imply

$$
\boxed{\widetilde D(v)\ge0.4133682545007734\,\|v\|_2^2.}
$$

With $v_0=\sqrt\rho$, $\|v_0\|_2=1$, the full-measure variance is
$\operatorname{Var}_\nu(U^{-1}v)=\|v\|_2^2-|\langle v,v_0\rangle|^2$.
Consequently the target form at $c=3/8$ satisfies

$$
\begin{aligned}
T_c(v)&=\widetilde D(v)
-c(\|v\|_2^2-|\langle v,v_0\rangle|^2)\\
&\ge0.0383682545007734\,\|v\|_2^2
+\tfrac38|\langle v,v_0\rangle|^2.
\end{aligned}
$$

This is a positive gap for the complete high-frequency restriction.
Every Gamma crossing edge, every prime power and the original mean
correction remain present. It supplies a coercivity input for eliminating
that block. The low-frequency block and its coupling still require
estimation on a common realization; this result does not establish
matrix PSD or exclude mixed low/high spectral vectors. There is no
cofinal-window, RH, Robin, originality or new Lean-certification claim.

## Reproduce

The recorded runtime is Python 3.13.12, python-flint 0.9.0 and 128-bit
ball arithmetic. From the repository root run

```sh
uv run --no-project --python 3.13.12 --with python-flint==0.9.0 python docs/reports/theta-mixed-matrix/joint_high_floor.py
```

The command writes `joint-high-floor-result.json` beside the program and
records the derivative supplier data's SHA-256. It rejects an uncertified
positive coefficient, invalid theta denominator or tail condition, or
failure of the declared joint floor $2/5$ and high-form threshold $3/8$.
Independent checking reproduced selected cells and checked the saved
cell arithmetic, aggregate minima and scalar supplier endpoints without
repeating the complete grid. This project-authored program reuses the
canonical theta setup and FLINT arithmetic; dependency licensing is
supplied by python-flint/FLINT.


The [saved joint-field weight](joint-weighted-input.md) retains these
pointwise cell floors before taking their scalar minimum. Its directed
output cap pays a smaller common weighted action-tail input for the same
actual $N=64,c=3/8$ correction map and old action cutoffs. No theta or
joint-floor grid is rerun; retained weighted Grams and matrix signs
remain unpaid.
