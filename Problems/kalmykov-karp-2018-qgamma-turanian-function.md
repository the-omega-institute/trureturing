---
slug: kalmykov-karp-2018-qgamma-turanian-function
bibkey: kalmykovkarp2018qgamma
doi: 10.1016/j.jmaa.2017.11.041
triage: theorem
motivation_gids:
  - D5/S3/Analytic/QGammaTuran/FunctionResult.result
url: https://arxiv.org/abs/1702.03788
---

# Refutation of reciprocal q-gamma function positivity

## Problem

S. I. Kalmykov and D. B. Karp, *Inequalities for series in q-shifted
factorials and q-gamma functions*, J. Math. Anal. Appl. 460 (2018),
332–351, DOI 10.1016/j.jmaa.2017.11.041, arXiv:1702.03788v1,
Conjecture 1, printed p. 12:

> All conclusions of Theorem 3 are valid for all α > 0, while conditions on other parameters remain intact. In particular, µ → g(µ; x) is log-concave for each fixed 0 < x < Rg.

Theorem 3, printed p. 11:

> For a real sequence {gₙ}ₙ≥₀ and fixed 0 < q < 1 define
>
> $g(\mu;x)=\displaystyle\sum_{n=0}^{\infty}\frac{g_nx^n}{\Gamma_q(\mu+n)}.$ (16)
>
> Suppose {gₙ}∞ₙ₌₀ is doubly positive. Then (16) has a positive radius of convergence Rg and the generalized Turánian
>
> $\Delta_g(\alpha,\beta;x)=g(\mu+\alpha;x)g(\mu+\beta;x)-g(\mu;x)g(\mu+\alpha+\beta;x)$
>
> is positive for 0 < x < Rg if α ∈ N, β > 0 and µ ≥ max(−β, −1). If, in addition, α ≤ β + 1, then Δg(α, β; x) has positive power series coefficients at all powers of x.

Equation (6), printed p. 4:

> The q-gamma function is defined by
>
> $\Gamma_q(z)=(1-q)^{1-z}\displaystyle\frac{(q;q)_\infty}{(q^z;q)_\infty}$ (6)
>
> for |q| < 1 and all complex z such that qᶻ⁺ᵏ ≠ 1 for k ∈ N₀.

The reciprocal is extended by zero at nonpositive integers. Doubly
positive means nontrivial, nonnegative, log-concave and without internal
zeros, as on printed p. 3. The function assertion has no
$\alpha\le\beta+1$ restriction.

### Formal reading

The names below belong to `D5.S3.Analytic.QGammaTuran.FunctionResult`,
except for the reused reciprocal and sequence condition.

| Source object | Lean name | Correspondence |
| --- | --- | --- |
| Reciprocal of (6) | `Result.rqgamma` | The same real infinite-product quotient as in the coefficient settlement. |
| Doubly positive sequence | `D5.S3.Analytic.ReciprocalGammaTuran.Defs.AdmissibleSeq` | Nontriviality, nonnegativity, log-concavity and no internal zeros. |
| Series (16) | `qseries` | The real infinite sum, in the printed order of factors. |
| Radius of (16) at the given $\mu$ | `radius` | Mathlib scalar-series radius in $[0,\infty]$, for coefficients $g_n\,\texttt{rqgamma}(q,\mu+n)$. |
| Function clause | `claim` | All permitted parameters and every $0<x<R_g$, with $R_g=\texttt{radius}\ q\ \mu\ g$. |
| Refutation | `result` | Exactly $\neg\,\texttt{claim}$. |

The radius is taken for series (16) at the theorem's given $\mu$.
As the source states on printed p. 12, “Writing Rg > 0 for the radius
of convergence in (16), we claim that the next conjecture is true.”
Mathlib's `FormalMultilinearSeries.ofScalars` represents its coefficient
sequence, and `FormalMultilinearSeries.radius` supplies the standard
extended nonnegative radius. For this scalar series the coefficient-map
norm is exactly the absolute value of the coefficient.

At the example, absolute summability at $x=3/2$ gives $3/2\le R_g$.
Thus $0<93/100<3/2\le R_g$, so the refutation holds strictly inside
the disk of convergence of (16). The same geometric comparison proves
summability of all four shifted series at $x=93/100$.

## Motivation

The settling declaration is
`D5/S3/Analytic/QGammaTuran/FunctionResult.result`.
The source note is `D5/L/Asymptotics/kalmykovkarp2018qgamma`.
A negative power-series coefficient alone need not produce a negative
function value. This assertion concerns the convergent function itself.

## Gap

**PROVED** (`D5.S3.Analytic.QGammaTuran.FunctionResult.result`): the
function clause is false. The example is $g_n=1$, $q=(93/100)^{10}$,
$\mu=-7/10$, $\alpha=3/10$, $\beta=7/10$, $x=93/100$.
The boundary equality $\mu=\max(-\beta,-1)$ is permitted, and
$\alpha$ is positive and nonintegral. Log-concavity restricted to nonnegative parameters $\mu$ remains **OPEN**.

## Route

Put $P(a)=(a;q)_\infty$, $y=x(1-q)$ and

$$H(a,y)=\sum_{n\ge0}y^nP(aq^n).$$

The reciprocal-product formula gives

$$g(s;x)=\frac{H(q^s,y)}{P(q)(1-q)^{1-s}}.$$

All terms after index zero are nonnegative when $s\ge-1$, and their
magnitudes are bounded geometrically for $0\le y<1$.
For $0\le a\le1$,

$$\prod_{j<N}(1-aq^j)\left(1-\frac{aq^N}{1-q}\right)
\le P(a)\le\prod_{j<N}(1-aq^j).$$

The first ten normalized series terms use these bounds with six
product factors each. The remaining series is at most $y^{10}/(1-y)$.
Separating the first term gives
$H(a,y)=P(a)+yH(aq,y)$, and $P(a)=(1-a)P(aq)$.
Thus the positive-parameter estimates at $a=r^3,r^6,r^{10}$,
$r=93/100$, also bound the negative shifts and the pole at zero.
The normalized products obey

$$H(r^{-4},y)H(1,y)\le0.151552931931<0.151590196222
\le H(r^{-7},y)H(r^3,y).$$

Both original products have the same positive denominator
$P(q)^2(1-q)^{12/5}$. Their difference is strictly negative.

## Falsifier

One admissible sequence and permitted parameter choice with a
nonpositive function value contradict the universal strict positivity
assertion. The displayed value is strictly negative. An error in the
normalization, convergence argument or finite rational bounds would
invalidate this refutation without proving the source assertion.

## Evidence

**PROVED**: `D5.S3.Analytic.QGammaTuran.FunctionResult.result` has the
closed type `¬ claim`. The proof reuses `Result.qprod` and
`Result.rqgamma` (definitions),
`D5.S3.Analytic.ReciprocalGammaTuran.Defs.admissible_one`, and
`D5.S3.Factorization.JordanCototientRecordLimitInfinity.one_sub_prod_le_sum`.
Here `Result` denotes `D5.S3.Analytic.QGammaTuran.Result`.
`FunctionResult`'s private helpers derive the product estimates and the
reciprocal-product identity from these declarations and pinned Mathlib.

**COMPUTED**: the immutable
[q-gamma experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/159884137a4ec45e1f49000bc46b2cac5958eae7/experiments/kalmykov-karp-qgamma-turanian)
contains both scripts below.

- `python3 kk-qgamma-fcert.py 93`, exit code 0; SHA-256
  `45cddfed518e203d4996d02d1741ba41477a092cd94094cf7fb6b9cddb11c2c1`.
  Rational intervals are rounded outward to multiples of $2^{-160}$;
  interval products use all four endpoint products. The script bounds
  each infinite product with 120 factors and a geometric tail loss,
  propagates term intervals through 160 recurrence steps, and bounds
  the remaining series by a geometric tail using its eventual sign.
  At $x=93/100$, the two normalized product enclosures print as
  $[0.149311098,0.149311098]$ and $[0.152952715,0.152952715]$.
  The exact rational endpoint comparison prints
  `certified Delta < 0: True`. The printed decimals are rounded
  displays of intervals of positive width, separate from the Lean bounds above.
- `python3 kk-qgamma-function-scan.py 0.5 0.9`, exit code 0; SHA-256
  `3d2381f0242f497f18515986fd86626b5a8731ba0d1bd36a916576da18a25937`.
  The scan uses 25 decimal digits, the six parameter triples in the
  script and $x=Rk/60$ for $1\le k\le59$, where $R=1/(1-q)$.
  At $q=0.5$ and $(-0.7,0.3,0.7)$ it finds relative Turanian
  approximately $-0.013036$ at $x\approx0.9333$.
  At $q=0.9$ and $(-0.7,0.7,0.7)$ it finds approximately
  $-0.0022595$ at $x\approx1.667$.
  For the four tested triples with $\alpha=\beta$, the $q=0.5$
  grid contains no negative value. These are finite numerical readings.

The supplied literature scope comprises the cited-by works recorded for
OpenAlex W2603745271: arXiv:1808.05105 and its 2019 journal version
supply no settlement in that scope; DOI 10.1142/s1793042120400187
treats a different q-binomial question. The classical reciprocal Gamma
refutations concern $q=1$. No settlement was found in the supplied
Formal Conjectures and conjectures.io scope. This bounded search does
not establish exhaustive coverage or priority.

## Triage

### What the settlement shows

- **PROVED** (`D5.S3.Analytic.QGammaTuran.FunctionResult.result`):
  the function clause fails for the displayed constant-sequence example
  at a point strictly inside the disk of convergence of (16):
  $0<93/100<3/2\le R_g$.
  A permitted negative initial shift produces one negative reciprocal
  q-gamma term before a positive tail; the two shifted products do not
  preserve the conjectured order.
- **COMPUTED**: the function clause already fails at $q=1/2$ for
  $(\mu,\alpha,\beta)=(-7/10,3/10,7/10)$, according to the function
  scan in Evidence.
- **COMPUTED**: with $\alpha=\beta$, the function scan finds failures
  at $q=0.9$, whereas its $q=1/2$ grid has no negative value. The
  tested range and computation details are those in Evidence.
- Consequence in prose of
  `D5.S3.Analytic.QGammaTuran.FunctionResult.witness_negative`:
  at the displayed $q,x$ and $g_n=1$, log-concavity on any interval
  containing $[-7/10,3/10]$ is impossible. Indeed,
  $-2/5=(7/10)(-7/10)+(3/10)(3/10)$ and
  $0=(3/10)(-7/10)+(7/10)(3/10)$.
  Log-concavity at these convex combinations, with respective weights
  $3/10$ and $7/10$ on the right endpoint, would give
  $g(-2/5;x)g(0;x)\ge g(-7/10;x)g(3/10;x)$ after multiplication.
  The endpoint values are strictly positive by the normalized lower
  bounds and positive denominators. This contradicts the proved strict
  reverse inequality. This consequence is not a separate Lean theorem.
- **OPEN**: log-concavity restricted to nonnegative parameters $\mu$
  is not decided by this witness or by the finite scans.
- **OPEN**: uniform intervals in q, positivity on a whole continuum
  when $q=1/2$ and $\alpha=\beta$, and the remaining conjectural
  extensions receive no conclusion from these observations.
  Theorem 3's integral-shift statement is outside the example's
  parameter choice.

## ASSUMED-UNVERIFIED

Exhaustive literature coverage, citation-index completeness and priority
are unverified. The bounded literature scope is supplied bibliographic
evidence; no current network search is asserted. The finite scan uses
truncated products and floating arithmetic, so its readings are not
uniform signs on a continuous parameter range.
