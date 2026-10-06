# Signed arithmetic heads and fixed-row tail allowances

The [pole-cancelled window](centered-window.md) identifies a sufficient
all-test estimate but does not supply it. The arithmetic remainder can
be kept as one signed prime-minus-continuum object. Published cumulative
and smoothing estimates then supply two more specific inputs: a tail
allowance for a fixed compact low row, and a finite-head band allowance
that preserves cross terms. Neither input establishes the low-block sign
or the cofinal comparison.

The source criteria, Plancherel mechanism and original theta/domain
suppliers are reused. The parameter maps and directed finite-head
calculation below are paper and experimental applications, with no new
general criterion, Lean certification or priority claim.

## Preserve the sign of the complete remainder

Use the original $w=\ell/\Phi$, $\ell=2\cosh(x/2)$ and
$w_*=2/\sup_{\mathbb R}\Phi>0$. For centered compact even $f$,
$\|f\|_w^2=\int w|f|^2$ is the original $B_L[f']$, including the
constraint which makes the mean subtraction zero.
Every Fourier transform here is the unnormalized angular transform
$F_f(\xi)=\int f(x)e^{-i\xi x}dx$.

Put

$$
E(t)=\Psi(e^t)-e^t,\qquad
d\mu(t)=e^{-t/2}dE(t)
=\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}\delta_{\log n}(dt)
-e^{t/2}dt\quad(t>0),
$$

and $C_f(t)=\int f(x+t)\overline{f(x)}dx$.
For even complex $f$, this correlation is real and even. For compact
$f$ it also has compact support, so

$$
\mathcal R(f)=\int_0^\infty[C_f(t)+C_f(-t)]d\mu(t)
$$

is a well-defined complete prime-discrepancy pairing.
The retained [Suzuki complete formula](../../../Library/Weil/suzuki2026screw.md),
arXiv:2606.09096v3, Section 2.4 following (2.7) and Section 2.5,
(2.9)–(2.11), has the negative prime-correlation sign. On
$F_f(\pm i/2)=0$ it gives

$$
Q_W(f)=\mathcal H(f)-\mathcal R(f),\qquad
\mathcal H(f)=\frac1{2\pi}\int_{\mathbb R}
\left[\Re\psi_\Gamma\left(\frac14+\frac{i\xi}{2}\right)
-\log\pi+\frac1{\xi^2+1/4}\right]|F_f(\xi)|^2d\xi. \tag{SD1}
$$

Here $\psi_\Gamma=\Gamma'/\Gamma$.
To check the rational term's sign, the exact pole constraint gives
$\int2\cosh(t/2)C_f(t)dt=0$. Thus the continuous main term
$\int e^{|t|/2}C_f(t)dt$ equals
$-\int e^{-|t|/2}C_f(t)dt$. The latter kernel has transform
$1/(\xi^2+1/4)$, producing the plus sign in (SD1).
The underlying complex moment identity is
$\int e^{st}C_f(t)dt=F_f(is)\overline{F_f(-is)}$.

The required relative estimate is an upper bound

$$
\mathcal R(f)\le\mathcal H(f)+\varepsilon_j\|f\|_w^2
\quad\text{for every centered even compact smooth }f
\text{ supported in }(-L_j,L_j),\quad
L_j\to\infty,\quad\varepsilon_j\to0. \tag{SD2}
$$

This remains unproved. The multiplier in (SD1) at zero is
$4-\gamma-\pi/2-3\log2-\log\pi<0$, so the pole constraint does not
make $\mathcal H$ nonnegative. Positivity of a different discrepancy,
or a pointwise unsigned error envelope, does not supply (SD2).

## A fixed-row tail with the actual complement norm

Let $p,q$ be compact smooth primitives, with
$\operatorname{supp}p\subset[-a,a]$, $a\ge0$. Let $A\ge\log2$
avoid the logarithms of integers. Define

$$
H_{p,q}(t)=\int[p(x+t)+p(x-t)]\overline{q(x)}dx,
\qquad
\mathcal R_{>A}(p,q)=\int_{(A,\infty)}e^{-t/2}H_{p,q}(t)dE(t).
$$

The head includes $\log n\le A$ and the tail excludes it.
Stieltjes integration retains the endpoint:

$$
\mathcal R_{>A}(p,q)
=-e^{-A/2}E(A)H_{p,q}(A)
-\int_A^\infty E(t)e^{-t/2}
\left[H'_{p,q}(t)-\frac12H_{p,q}(t)\right]dt. \tag{SD3}
$$

Its derivative is
$H'_{p,q}(t)=\int[p'(x+t)-p'(x-t)]\overline{q(x)}dx$.
It falls on the chosen low row; no derivative budget is required of
the arbitrary complement vector. Compact correlation removes the
boundary at infinity.

Write

$$
\begin{aligned}
J_0(p,t)&=\left\|\frac{p(\cdot+t)+p(\cdot-t)}{\sqrt w}\right\|_2,\\
J_1(p,t)&=\left\|\frac{p'(\cdot+t)-p'(\cdot-t)
-[p(\cdot+t)+p(\cdot-t)]/2}{\sqrt w}\right\|_2.
\end{aligned}
$$

The [Johnston–Yang supplier](../../../Library/Weil/johnstonyang2022pnt.md)
gives $|E(t)|\le e^t\epsilon(t)$ for $t\ge\log2$, with
$\epsilon(t)=9.39t^{1.515}e^{-0.8274\sqrt t}$.
Weighted Cauchy–Schwarz in (SD3) yields

$$
|\mathcal R_{>A}(p,q)|\le\mathfrak C_A(p)\|q\|_w,
\qquad
\mathfrak C_A(p)=e^{-A/2}|E(A)|J_0(p,A)
+\int_A^\infty e^{t/2}\epsilon(t)J_1(p,t)dt. \tag{SD4}
$$

For centered $q$, $\|q\|_w^2=B_L[q']$, so the complement is measured
in the original metric. The estimate itself does not require centering;
that constraint is needed for this identification with $B_L$.
All atoms, the continuous main term and the endpoint use the same $E$.

The retained [original-series theta bound](../../../Library/Analytic/romik2021orthogonal.md#explicit-original-series-majorants)
is $\Phi(x)\le(144/5)e^{-(3/2)e^{2|x|}}$. For $t\ge a$ it gives

$$
\begin{aligned}
J_0(p,t)&\le2\|p\|_2\sqrt{72/5}\,e^{-(3/4)e^{2(t-a)}},\\
J_1(p,t)&\le(2\|p'\|_2+\|p\|_2)\sqrt{72/5}\,e^{-(3/4)e^{2(t-a)}}.
\end{aligned}
$$

For $A\ge\max(\log2,a+1)$, set
$d_A=(3/2)e^{2(A-a)}-1/2-1.515/A>0$.
The logarithmic derivative of
$m(t)=t^{1.515}e^{t/2-0.8274\sqrt t-(3/4)e^{2(t-a)}}$
is at most $-d_A$ for $t\ge A$. Therefore

$$
\mathfrak C_A(p)\le
9.39\sqrt{72/5}\,A^{1.515}
e^{A/2-0.8274\sqrt A-(3/4)e^{2(A-a)}}
\left[2\|p\|_2+\frac{2\|p'\|_2+\|p\|_2}{d_A}\right]. \tag{SD5}
$$

This tends to zero for each fixed compact low row, uniformly in the
support radius of $q$. A finite $w$-orthonormal row family has the
coefficient allowance $(\sum_\alpha\mathfrak C_A(p_\alpha)^2)^{1/2}$.
Growing row families still need uniform support and derivative budgets.
The existing Lenz bounds (BD), (BT) and (JL) already control complete
weighted prime graphs; (SD5) is not a claimed numerical improvement
over those different operator estimates.

## Retain the signed finite head inside one square

Define the finite real even measure and its angular transform by

$$
\begin{aligned}
\mu_A={}&\sum_{\log n\le A}\frac{\Lambda(n)}{\sqrt n}
(\delta_{\log n}+\delta_{-\log n})
-\mathbf1_{\{|t|\le A\}}e^{|t|/2}dt,\\
\sigma_A(\xi)&=\int e^{-i\xi t}d\mu_A(t),\qquad
V_A=\|\mu_A\|_{\rm TV}.
\end{aligned}
$$

For $C_\delta(t)=(1-|t|/\delta)_+$, the
[weighted Gallagher mechanism](../../../Library/Weil/coppolalaporta2015gallagher.md)
and the same Plancherel identity give

$$
\int_{-T}^T|\sigma_A(\xi)|^2d\xi
\le U_A(T):=
\frac{2\pi}{\delta^2\operatorname{sinc}^4(\delta T/2)}
\int_{\mathbb R}|C_\delta*\mu_A(t)|^2dt,
\qquad 0<\delta T<2\pi. \tag{SD6}
$$

This finite signed-measure application retains its continuous component;
it is not quoted as the source's verbatim discrete theorem.
Its squared integral contains prime–prime, prime–continuum and
continuum–continuum contributions. Independently replacing those
terms by unrelated extrema would change the measure.

For a row $p$, the actual finite-head coupling obeys

$$
\|\mu_A*p\|_{L^2(w^{-1}dx)}^2
\le\frac1{2\pi w_*}
\left[\|F_p\|_{L^\infty[-T,T]}^2U_A(T)
+V_A^2\int_{|\xi|>T}|F_p(\xi)|^2d\xi\right]. \tag{SD7}
$$

Pairing with $q$ multiplies the square root by $\|q\|_w$.
The factor $1/(2\pi w_*)$ uses the stated unnormalized $F_p$;
with a unitary Fourier transform that outside factor changes.
The out-of-band term remains present. A better band allowance alone
does not measure the complete improvement for a particular row.

## New arithmetic examples at three FIB cutoffs

The [directed producer](signed_head.py) and [saved data](signed-head-result.json)
use $\delta=1/8$ and exact cutoffs
$X=F_6+1/2,F_9+1/2,F_{12}+1/2$, with $A=\log X$.
These cuts avoid prime-power endpoints and retain every prime power
$n\le\lfloor X\rfloor$. The Fibonacci schedule chooses resolutions;
it does not supply a Fibonacci-to-prime intertwiner or (SD2).

Let $S_-=\|C_\delta*\mu_A\|_2^2$ and let $S_+$ be the same square
after changing the negative continuous component to positive.
If $P$ denotes the smoothed atoms and $J$ the smoothed continuum, the
calculation keeps

$$
S_-=\|P\|_2^2+\|J\|_2^2-2\langle P,J\rangle,
\qquad S_+=\|P\|_2^2+\|J\|_2^2+2\langle P,J\rangle.
$$

All components are integrated on their complete piecewise supports.
The six preregistered band checks compare $U_A(T)$ with the valid
same-measure total-variation allowance $2TV_A^2$, for $T=8,16$.
At $T=16$, outward enclosures are:

| $X$ | Positive prime-power atoms | $S_-/S_+$ | $U_A(16)/(32V_A^2)$ |
|---|---:|---:|---:|
| $17/2$ | 6 | $[0.14661455,0.14661457]$ | $[0.01806632,0.01806634]$ |
| $69/2$ | 18 | $[0.05745728,0.05745730]$ | $[0.00435053,0.00435054]$ |
| $289/2$ | 47 | $[0.02007467,0.02007469]$ | $[0.00118204,0.00118205]$ |

The saved 192-bit directed intervals certify all six allowance ratios
below one. These are upper allowances, not actual band energies or
positive lower bounds. They improve the indicated band part relative
to its total-variation envelope; no comparison to the existing
complete theta action or prime-graph budgets is claimed.

```sh
uv run --no-project --python 3.13.12 --with python-flint==0.9.0 python docs/reports/theta-mixed-matrix/signed_head.py
```

The program is project-authored and uses python-flint/FLINT. It rejects
insufficient precision, uncertified interval order, a lost common-measure
account or an uncertified improvement. A midpoint sort only proposes
the order; every adjacent breakpoint comparison uses directed intervals.
No old theta action, matrix or numerical target is recomputed.

To reach the cofinal goal, the retained low-block sign, row Fourier
band/tail budgets, complete high–high comparison and growing low-family
constants must be paid on one common parameter sequence. Fixed-row
convergence in (SD5) and three finite heads do not supply that sequence.
The original arithmetic lower comparison, RH and full Robin remain
unresolved.

The [complete fixed-band row allowance](signed-low-row.md) supplies
the row Fourier budget and full arithmetic tail for the original
$p=sv$ low unit ball at $N=64$, with new $T=128,192$ and $\delta=1/64$.
It retains both Fourier expenses and improves only the stated
same-measure weighted total-variation reference. The low sign and
growing-band common comparison remain unproved.
