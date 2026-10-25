---
bibkey: guloglunevans2008beatty
authors: Ahmet M. Güloğlu; C. Wesley Nevans
year: 2008
title: Sums of multiplicative functions over a Beatty sequence
doi: 10.1017/S0004972708000853
url: https://arxiv.org/abs/0801.2796v1
claim: "Theorem 1 controls multiplicative-function sums on a finite-type Beatty sequence. Applied to sigma(n)/n and the existing canonical unit-bit bridge, it gives a same-integer weighted branch average, without a bound for an individual extremal candidate."
strata_touched: []
license: citation-only
triage: anchor
---

# Multiplicative Beatty sums and the canonical FIB unit bit

Bull. Austral. Math. Soc. **78** (2008), 327–334. The inspected primary
text is the [published article](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/S0004972708000853).
Its title uses “of”; [arXiv:0801.2796v1](https://arxiv.org/pdf/0801.2796v1)
uses “with”. The function class and Theorem 1 agree in these versions.
The source statement, parameter conditions and application below were
checked; the complete analytic proof was not independently verified.
The applications are paper derivations without new Lean declarations,
Lean verification or an originality claim.

## The source theorem and its fixed function class

Printed p.327 defines, for a fixed $A\ge1$, the class $\mathcal F_A$ of
multiplicative functions satisfying

$$
|f(p)|\le A\quad(p\text{ prime}),\qquad
\sum_{n\le N}|f(n)|^2\le A^2N\quad(N\in\mathbb N_{>0}).
$$

For $\alpha>1$ and real $\beta$, put
$B_{\alpha,\beta}=\{\lfloor\alpha k+\beta\rfloor:k\in\mathbb Z\}$.
**Theorem 1, printed p.328**, assumes that $\alpha$ is irrational of
finite Diophantine type and gives

$$
\sum_{\substack{n\le N\\n\in B_{\alpha,\beta}}}f(n)
=\alpha^{-1}\sum_{n\le N}f(n)
+O_{\alpha,A}\!\left(\frac{N\log\log N}{\log N}\right).
\tag{1}
$$

All sums over $n$ use positive integers. The implied constant depends
only on $\alpha,A$, so the statement is uniform in $\beta$ and in
$f\in\mathcal F_A$. It does not remove the dependence on $A$ for a
family whose second moments grow with $N$.

## Reusing the existing canonical observation

Let $\varphi=(1+\sqrt5)/2$, $\psi=1-\varphi$, and $a=2-\varphi$.
For the actual canonical Zeckendorf representation of $n>0$, let
$h(n)\in\{0,1\}$ indicate whether the unit term is present. It is not
the occupancy of the numerical term 2. The existing
[Zeckendorf–Beatty bridge](../../D5/S1/Words/ZeckendorfBeattyBridge.lean)
uses Fibonacci **index** 2, namely $F_2=1$, and the existing
[mechanical-word window](../../D5/S1/Words/GoldenMechanicalWord.lean)
identifies its complement. Their application gives

$$
h(n)=1\iff a<\{n\varphi\}<2a
\iff n=\lfloor k\varphi^2-1\rfloor\quad\text{for some }k\ge1.
\tag{2}
$$

The positive values of $B_{\varphi^2,-1}$ come exactly from $k\ge1$.
The Beatty correspondence is reused, rather than a new numeration
theorem; the [Dekking entry](../Words/dekking2023structure.md) already
points to the repository's canonical bridges.

Write $n=h+2A+3B$ using the complete composition $(A,B)$ after removing
the unit. Put $c=4A+7B$, $m=\lfloor n\varphi\rfloor$,
$r=\{n\varphi\}$ and $E=c-\sqrt5(n-h)$. The existing
[displacement reading](../../D5/S1/Deficit/ZeckendorfDisplacementReading.lean),
applied at $n-h$, gives $c=2(\lfloor(n-h+1)\varphi\rfloor-1)-(n-h)$.
Its integer lifts and residuals are therefore

| Actual rotation window | $h$ | $c$ | $E$ |
|---|---:|---|---|
| $0<r<a$ | 0 | $2m-n$ | $-2r$ |
| $a<r<2a$ | 1 | $2m-n-1$ | $2(\varphi-1-r)$ |
| $2a<r<1$ | 0 | $2m-n+2$ | $2(1-r)$ |

No positive integer hits an endpoint. The parity condition is retained:
$c\equiv n-h\pmod2$, and the original integer composition is recovered
by $B=c-2(n-h)$ and $A=(7(n-h)-3c)/2$. For $n=1$, these formulas give
$h=1,A=B=E=0$; any argument requiring nonzero composition must exclude
that case separately.

## A weighted average for the same arithmetic integer

Take $Z(n)=\sigma(n)/n$. It is multiplicative and
$Z(p)=1+1/p\le3/2$. The source already supplies

$$
\sum_{n\le N}\frac{\sigma(n)^2}{n^2}
=\frac52\zeta(3)N+O((\log N)^3)
$$

in **printed p.333, proof of Corollary 4**. This implies the required
second-moment bound for some fixed $A$: enlarge it to cover the finite
initial range. No new second-moment theory is needed. Since the quadratic
irrational $\varphi^2$ has finite type, (1) and (2) yield

$$
\sum_{\substack{n\le N\\h(n)=1}} Z(n)
=\varphi^{-2}\sum_{n\le N}Z(n)
+O\!\left(\frac{N\log\log N}{\log N}\right).
\tag{3}
$$

This keeps the canonical unit bit and the multiplicative response of
the **same** integer. It is not an average over independently selected
Fib addresses and factorizations. Nevertheless its allowed error
exceeds even the elementary single-term upper bound
$Z(n)\le1+\log n$. It does not bound the maximum within either unit
branch. Replacing $Z$ by $Z\mathbf1_{\rm CA}$ or
$Z\mathbf1_{\rm SA}$ does not preserve the theorem's multiplicativity
hypothesis. Growing moments such as $Z^s$ require a fresh bound for
their function-class constant and its effect on the error.

## The small-discriminant condition needs shrinking rotation windows

Using the same complete composition, put
$Q=A^2+AB-B^2$ and $D=5h^2-4Q$. The existing affine certificate in
[the FIB theory, §202](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md)
gives

$$
D=5h^2+E\bigl(2\sqrt5(n-h)+E\bigr).
\tag{4}
$$

For $n\ge2$ and $L\ge0$, $c\ge2(n-h)$ implies the necessary bound

$$
|D|\le L\ \Longrightarrow\
|E|\le\frac{L+5}{(2+\sqrt5)(n-1)}.
\tag{5}
$$

Thus at $n\asymp X$ the raw-discriminant condition
$|D|\le(\log n)^K$ needed by the
[nonresidue cutoff](../Scale/pollack2017nonresidues.md) lies in rotation
windows of width $O((\log X)^K/X)$. The fixed unit window in (3) is a
different resolution. Neither (3) nor (5) forces an actual CA/SA
candidate into such a shrinking window, proves nonsquareness, or bounds
the squarefree kernel of $D$. Those joint arithmetic conditions remain
missing.

## Actual harmonic divisor weights on the FIB boundary

The same uniform function class also applies inside one actual divisor
inventory. This application uses (3), §2.2 and §3.1 of the
[2008 author version](https://arxiv.org/abs/0801.2796v1), whose PDF has
SHA-256 `d73fe4f68874f99b25f7eb9c95bc59f91c6c44c6359082c5cb0ad15840833db3`,
the already recorded DMS low-address detection, and the classical smooth
Euler-product tail. The labels below belong to each divisor $d$ of $N$;
they are not the digits of $N$ itself.

For sufficiently large real $P$ and positive integer $N$ with
$P^+(N)\le P$, put $\ell=\log P$ and define the circle probability measure

$$
Z(N)=\sum_{d\mid N}\frac1d,\qquad
\nu_N=\frac1{Z(N)}\sum_{d\mid N}\frac1d\,\delta_{\{d\varphi\}}.
$$

Uniformly over every circle interval $I$ and every such $N$, the
published inputs give the absolute comparison

$$
\left|\sum_{d\mid N}\frac{\mathbf1_I(\{d\varphi\})}{d}
          -|I|Z(N)\right|\ll(\log\ell)^2.
\tag{D1}
$$

If in addition $C_P=\operatorname{lcm}(1,\ldots,\lfloor P\rfloor)$
divides $N$, then

$$
\sup_I|\nu_N(I)-|I||\ll\delta_P,
\qquad \delta_P:=\frac{(\log\ell)^2}{\ell}\longrightarrow0.
\tag{D2}
$$

This includes the complete inventories at the SA sources recorded in
[the Segovia note](segovia2026partitions.md). It requires neither an
average over different $N$ nor independent prime-exponent sampling.

### Use the actual inventory in the uniform source class

For fixed $N$, the function $f_N(m)=\mathbf1_{m\mid N}$ is
multiplicative and satisfies $|f_N(p)|\le1$ and
$\sum_{m\le t}|f_N(m)|^2\le t$. Thus $f_N\in\mathcal F_1$, with
class constant independent of $N$. The theorem's count estimate can
therefore be used when both $N$ and its observation cutoff change.
The introduction's discussion of a main term exceeding the error is
not an additional hypothesis of Theorem 1. In particular finite support
of a fixed $f_N$ does not invalidate its uniform error bound.

For arbitrary $I$ one uses the source's Fourier proof, rather than
identifying Theorem 1 itself with an arbitrary-interval theorem. Keep
the rotation carrier $\eta=\varphi-1$ fixed and let the interval length
$b$ and position vary independently. In §2.2's Vinogradov smoothing,
take $\Delta=(\log t)^{-2}$ and $K=(\log t)^3$. For
$2\Delta\le b\le1-2\Delta$, the smoothed mean is $b$ and its
nonconstant coefficients satisfy the printed uniform bound
$|g(k)|\ll\min(|k|^{-1},|k|^{-2}\Delta^{-1})$.
The rational-approximation and Montgomery--Vaughan step in §3.1
depends only on the fixed finite-type carrier, $k$ and the function
class, so gives $S_{k\eta,f_N}(t)\ll t/\log t$ on the required
frequencies. Position only multiplies these terms by unit phases.
The same printed error balance consequently gives

$$
A_N(t,I):=\sum_{\substack{d\mid N\\d\le t}}
  [\mathbf1_I(\{d\varphi\})-|I|]
\ll\frac{t\log\log t}{\log t},\qquad t\ge e^e,
\tag{D3}
$$

with constant independent of $I,N$. For $b<2\Delta$, the bound
$f_N\le1$ and Lemma 1's unweighted golden-rotation discrepancy give
$O(\Delta t+t^{1/2})$, which is absorbed by (D3). Apply the same
argument to the complement when $1-b<2\Delta$. Endpoint conventions
change a count by at most two, since the positive integer rotations
are distinct. Thus no lower bound on $b$ remains in (D3).

Abel summation, with the initial bounded range absorbed in $O(1)$,
gives uniformly in $I,N$

$$
\left|\sum_{\substack{d\mid N\\d\le X}}
\frac{\mathbf1_I(\{d\varphi\})-|I|}{d}\right|
\ll1+\int_{e^e}^X\frac{\log\log t}{t\log t}\,dt
\ll1+(\log\log X)^2.
\tag{D4}
$$

For the complete tail, reuse the tilted Euler-product estimate from
Tenenbaum 2015, Lemma 2.2, with the classical Mertens product and
Rankin's inequality, as in the Segovia interface: for
$\sigma=1-1/\ell$ one has $\zeta(\sigma,P)\ll\ell$ and hence

$$
T(P,P^u):=\sum_{\substack{P^+(m)\le P\\m>P^u}}\frac1m
\le e^{-u}\zeta(\sigma,P)\ll\ell e^{-u},\qquad u\ge0.
$$

Every actual divisor omitted from (D4) belongs to this tail. Choose
$X=P^{3\log\ell}$. Its contribution to the centered sum is at most
$T(P,X)\ll\ell^{-2}$, while $\log\log X=O(\log\ell)$.
This proves the paper comparison (D1). When $C_P\mid N$, every
positive integer at most $\lfloor P\rfloor$ divides $N$, so
$Z(N)\ge H_{\lfloor P\rfloor}\ge\log P$. Division gives (D2)
without requiring a fresh precise asymptotic for the actual inventory.

### The five labels and a growing legal resolution

Reuse the [DMS circle detection and eight-address table](../Fourier/drmotamullnerspiegelhofer2025primes.md#the-actual-five-window-prime-frequencies-and-the-retained-unit).
A legal prefix $B$ of $r\ge1$ windows has circle mass $\mu_B$.
Keeping the separate unit digit gives one interval, with
$\mu_B\in\{\varphi^{-(3r+1)},\varphi^{-(3r+2)}\}$;
forgetting only that unit gives at most two intervals and still
$\mu_B\ge\varphi^{-(3r+2)}$. The same intervals detect the digits
of each actual divisor $d$, without restricting $d$ to primes.
Consequently (D2) gives, with constants independent of $B,r,N$,

$$
\left|\frac{\nu_N(B)}{\mu_B}-1\right|
\ll\varphi^{3r+2}\delta_P.
\tag{D5}
$$

The resulting joint prefix laws also converge in total variation:
the legal cylinders partition the circle, so their number is at most
$\varphi^{3r+2}$ and

$$
\frac12\sum_B|\nu_N(B)-\mu_B|
\ll\varphi^{3r+2}\delta_P.
\tag{D6}
$$

For every fixed $0<\varepsilon<1$, both errors tend to zero uniformly
on the complete-inventory class when

$$
r\le(1-\varepsilon)\frac{\log\log P}{3\log\varphi}.
\tag{D7}
$$

At $r=1$, the existing table's unconditional and unit-conditioned
columns therefore apply to reciprocal-divisor weights as well.
For example, conditional on $h(d)=0$, the limiting weights of
$[null,2,3,2\ 5,5]$ are

$$
(\varphi^{-3},\varphi^{-3},\varphi^{-3},
  \varphi^{-4},\varphi^{-4}).
$$

These are the already computed state-0 contraction length ratios.
Here they are transported to the arithmetic weights of one inventory;
no new interval partition or five-state counting proof is needed.

### The atom at one limits uniform relative resolution

The same actual measure has $\nu_N(\{\{\varphi\}\})\ge1/Z(N)$,
coming from the always present divisor $1$. Let $B_1(r)$ be its
legal prefix with the unit retained. DMS gives
$\mu_{B_1(r)}\le\varphi^{-(3r+1)}$, while the classical Mertens upper
bound supplies $Z(N)\le\prod_{p\le P}(1-1/p)^{-1}\ll\ell$. Hence

$$
\frac{\nu_N(B_1(r))}{\mu_{B_1(r)}}
\gg\frac{\varphi^{3r+1}}\ell.
\tag{D8}
$$

If $\varphi^{3r}/\log P\to\infty$, this ratio diverges. In
particular a depth above $(1+\varepsilon)\log\log P/(3\log\varphi)$
cannot have relative error tending to zero on every legal cylinder.
Together with (D7), this identifies the leading depth scale for that
specific uniform relative task. It does not assert an obstruction to
all finer metrics, adaptive observations or other divisor weights.

The measure describes the FIB addresses of divisors $d$, not a
restriction on the address of the original integer $N$. Its weights
sum exactly to one and its unnormalized weights still sum to $Z(N)$.
Redistributing them among geometric windows creates no upper bound
for that total. In particular, the absolute error allowance in (D1)
is much larger than an additive $P^{-1/2}$ allowance, so this estimate
cannot determine the Robin sign. This is an application of the published uniform
multiplicative-function method, classical tail bounds and existing
address detection, with no originality or Lean-verification claim.
