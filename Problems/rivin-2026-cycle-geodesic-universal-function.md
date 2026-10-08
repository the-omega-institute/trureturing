---
slug: rivin-2026-cycle-geodesic-universal-function
bibkey: rivin2026permanents
doi: null
url: https://arxiv.org/abs/2602.10141v3
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicScaling.result3
---

# Rivin's cycle-geodesic universal function

## Problem

Igor Rivin, “Permanents of matrix ensembles: computation, distribution, and
geometry”, arXiv:2602.10141v3, Section 8.4, Open Problem 3, states:

> Find a closed form for the universal function $f(t)$.

Observation 4 defines the finite-dimensional quantity as
$-n^{-1}\log|\operatorname{perm}\gamma_n(t)|$ for the literal matrix

$$\gamma_n(t)_{jl}=\frac{e^{2\pi it}-1}{n(e^{2\pi i(l-j+t)/n}-1)},\qquad j,l\in\{0,\ldots,n-1\}.$$

## Motivation

`D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicScaling.result3`
proves for every $0<t<1$, $t\ne1/2$,

$$
-\frac1n\log|\operatorname{perm}\gamma_n(t)|
\longrightarrow 1-\pi\delta\cot(\pi\delta),\qquad \delta=\min(t,1-t).
$$

At $t=1/2$, the rate tends to $1$ along $n=2m+1$. Along positive even
$n$ the permanent is zero. Endpoint value $0$ is the continuous extension
of the interior formula; it is not the value of the total Lean `universal`
definition at either endpoint. The settling theorem excludes endpoints.

## Gap

Preregistration [#13612](https://github.com/the-omega-institute/trureturing/issues/13612)
classifies both questions as Tier 1, quotes the published statements and gives
all quantifiers. Its bounded title, identifier, phrase, Borchardt and
product-formula searches report no explicit subsequent settlement. The exact
finite product itself is credited to Han (2000), DOI
10.1016/S0024-3795(00)00035-5. The algebraic input is a formalization of the
credited Gaudin identity, attested by Faribault–Schuricht (2012), DOI
10.1088/1751-8113/45/48/485202. Neither identity is claimed as a new literature
result. Their application supplies the two preregistered answers.

## Route

`GaudinPermanent.gaudin_permanent` identifies the reciprocal-difference
Cauchy permanent with a Gaudin determinant. Its proof differentiates Lagrange
interpolation and uses a determinant polynomial. A weighted Vandermonde
basis evaluates that determinant, yielding the literal cycle-geodesic product

$$
\operatorname{perm}\gamma_n(t)=n^{-n}\prod_{k=0}^{n-1}(n-k+kq),
\qquad q=e^{2\pi it},\quad n\ge1,\quad 0<t<1.
$$

At the midpoint the product reduces to $n^{-n}\prod_k(n-2k)$.
For positive even $n$ one factor vanishes. For odd $n$, a factorial
expression and the second-order Stirling estimate yield the uniform error
bound. Away from the midpoint, the logarithmic rate is a left Riemann sum
of $-\log|1-x+xe^{2\pi it}|$. Uniform continuity and evaluation of the
quadratic-logarithm integral give $1-\pi\delta\cot(\pi\delta)$.
The odd midpoint estimate supplies the remaining odd-dimensional limit.

## Falsifier

A falsifier for Problem 2 would violate the uniform odd-dimensional remainder
or the positive even-dimensional zero clause. A falsifier for Problem 3 would
be an interior nonmidpoint parameter whose rate has a different limit, or
failure of the odd midpoint limit. The kernel-checked conclusions exclude
these for the literal matrix and their stated domains. Endpoint evaluation of
the total Lean definitions and the empty permanent are outside those domains.

## Evidence

The four Lean modules and their Scribe mirrors are in
`D5/S3/Combinatorics/Permanental/CycleGeodesic/` and
`Blueprint/D5/S3/Combinatorics/Permanental/CycleGeodesic/`.
The settling declarations are `CycleGeodesicMidpoint.result2` and
`CycleGeodesicScaling.result3`; each settling Scribe node records its own
`OpenProblemResolutionClaim` with resolution `Proved`.
The axiom closure of every public declaration is contained in
$\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.
No new axiom or `sorry` is used. Each settling module has
`admission_basis: open-problem-resolution` (#13612; Proved).
Information-escape registration is paused under CLAUDE.md §3.9.

## Triage

### What the settlement shows

- **Proved:** the Han product holds for every positive dimension and every
  interior parameter, by `CycleGeodesicProduct.product_formula`. Its Gaudin
  input is credited to Faribault–Schuricht, rather than asserted as a new
  identity. The product replaces an exponential permutation sum by $n$
  explicit factors for this family.
- **Proved:** Open Problem 2 holds with the single constant $C=16$ for all
  positive odd dimensions; the permanent vanishes for all positive even
  dimensions, by `CycleGeodesicMidpoint.result2`. The positive-dimension
  convention is essential: at $n=0$ the empty permanent is $1$.
- **Proved:** Open Problem 3 has the interior closed form
  $1-\pi\delta\cot(\pi\delta)$ and odd midpoint limit $1$, by
  `CycleGeodesicScaling.result3`. All-dimension convergence excludes the
  midpoint, where the even permanent is zero. Endpoint value $0$ refers to
  the continuous extension of the interior expression: the total Lean
  function has `universal 0 = universal 1 = 1`, and `result3` excludes both
  endpoints. Reflection symmetry, the continuous endpoint extension and the
  $\pi^2t^2/3$ onset remain **open as separate Lean corollaries**.
- **Computed:** the next normalized midpoint coefficient approaches $1/18$
  in the five tested dimensions below. The full midpoint asymptotic series
  and even this next coefficient as a uniform theorem remain **open**;
  finite numerical evidence is not an asymptotic proof.
- **Open:** the DFT-geodesic prime-versus-composite dichotomy, Rivin's Open
  Problem 4, is not addressed. The two cycle-geodesic conclusions give no
  theorem about that distinct endpoint family.
- **Proved:** the exact product and its Stirling/Riemann consequences supply
  both answers without the source's suggested Ryser saddle-point analysis.
  Formalization of that alternative route remains **open**. The source's
  cycle-midpoint and interior-scaling observations become theorems in the
  stated domains; its other ensemble-distribution questions and Open
  Problem 4 remain open.

### Finite next-coefficient reading

At 80 decimal digits, evaluate

$$
n^2\left(\exp(L_n)-1-\frac1{3n}\right),\qquad
L_n=2\log\Gamma(n+1)-(n-1)\log2
-2\log\Gamma((n+1)/2)-(n+1)\log n+n-\log2.
$$

The tested scope is exactly $n\in\{101,201,401,1001,2001\}$.
These are numerical readings; no assertion about all odd $n$ follows.

| $n$ | Computed coefficient |
| --- | --- |
| 101 | 0.0551752740022157666346222726818 |
| 201 | 0.0553648015644500096126274046435 |
| 401 | 0.0554600269625193626369300240258 |
| 1001 | 0.0555173079603667562093490438847 |
| 2001 | 0.0555364257507125260616290303381 |

Command: `python3 next-coefficient.py` (exit $0$); SHA-256 `7ac75ef7ba32af85368f8d7a6a2b6aa22e3e14484a1dd3990e88f917d81a1f35`.
Save the following exact source as `next-coefficient.py`; its dependency is
`mpmath`.

```python
import mpmath as mp
mp.mp.dps = 80
for n in (101, 201, 401, 1001, 2001):
    log_ratio = (2 * mp.loggamma(n + 1) - (n - 1) * mp.log(2)
                 - 2 * mp.loggamma(mp.mpf(n + 1) / 2)
                 - (n + 1) * mp.log(n) + n - mp.log(2))
    coefficient = n**2 * (mp.exp(log_ratio) - 1 - mp.mpf(1) / (3 * n))
    print(n, mp.nstr(coefficient, 30))
```

## ASSUMED-UNVERIFIED

The literature non-settlement reading is bounded to the searches in #13612,
not an exhaustive priority certificate. The next-coefficient calculation is
numerical and finite. The full midpoint series, the three additional analytic
corollaries as Lean declarations, the alternative saddle-point route, and
Open Problem 4 remain open. The source's endpoint properties refer to
continuous extension, and the dimension convention is positive.
