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
