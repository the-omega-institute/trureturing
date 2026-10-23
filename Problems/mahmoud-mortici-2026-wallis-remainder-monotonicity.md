---
slug: mahmoud-mortici-2026-wallis-remainder-monotonicity
bibkey: mahmoudmortici2026wallisratio
doi: 10.1007/s00025-026-02697-2
triage: theorem
motivation_gids:
  - D5/S3/Analytic/WallisRemainder/Result.result
url: https://link.springer.com/article/10.1007/s00025-026-02697-2
---

# Strict monotonicity of Wallis gamma remainders

## Problem

Section 4, Open Question of the source identified in
`D5/L/Asymptotics/mahmoudmortici2026wallisratio` asks:

> Do the functions μ(x)=−x²−{(3/x)[ln(√x Γ(x+1/2)/Γ(x+1))]^{−1}+24}^{−1}, θ(x)=(23040x⁵/31){3x/(24x²+1)+ln(√x Γ(x+1/2)/Γ(x+1))}, χ(x)=(358400x⁷/257){(120x²+31)/(96x(10x²+3))+ln(√x Γ(x+1/2)/Γ(x+1))} satisfy the property that μ(x) and χ(x) are strictly increasing, while θ(x) is strictly decreasing for all x>0?

### Formal reading

All Lean names below have prefix `D5.S3.Analytic.WallisRemainder`.

| Source object | Lean name | Correspondence |
| --- | --- | --- |
| $B(x)=\sqrt{x}\,\Gamma(x+1/2)/\Gamma(x+1)$ | `Defs.wallisB` | The exact real Gamma quotient. |
| $\mu(x)$ | `Defs.mu` | The displayed nested reciprocal, with exactly the constants 3 and 24. |
| $\theta(x)$ | `Defs.theta` | The displayed difference multiplied by $23040x^5/31$. |
| $\chi(x)$ | `Defs.chi` | The displayed difference multiplied by $358400x^7/257$. |
| Implicit reciprocal conditions | First conjunct of `Defs.claim` | For every $x>0$, $\ln B(x)\ne0$ and $(3/x)[\ln B(x)]^{-1}+24\ne0$. |
| Strict monotonicity | Remaining conjuncts of `Defs.claim` | For every real $0<x<y$, $\mu(x)<\mu(y)$, $\theta(y)<\theta(x)$ and $\chi(x)<\chi(y)$. |
| Complete assertion | `Result.result : Defs.claim` | Unconditional theorem with no representation assumption. |

## Motivation

The settling declaration is `D5/S3/Analytic/WallisRemainder/Result.result`.
The source note is `D5/L/Asymptotics/mahmoudmortici2026wallisratio`.
Strict monotonicity determines the direction of improvement of three
normalized rational approximations to a Wallis-type Gamma quotient.

## Gap

Status: **Proved** for every positive real argument, with all three
strict comparisons and both reciprocal nonvanishing assertions.
No assertion at a nonpositive argument is included.

## Route

Put $r(x)=-\ln B(x)$. Gamma recurrence gives
$r(x)+r(x+1/2)=\frac12\ln((x+1/2)/x)$.
Log convexity gives $0\le r(x)\le\frac12\ln((x+1/2)/x)$, hence $r(x)\to0$.
The convergent integral

$$R(x)=\int_0^\infty e^{-xt}\frac{\tanh(t/4)}{2t}\,dt$$

obeys the same half-step equation and tends to zero. The difference
$r-R$ is periodic with period one and tends to zero, so $r=R$.

The cotangent partial fractions on the imaginary axis yield

$$\frac{\tanh u}{u}=\sum_{n\ge0}\frac8{\pi^2(2n+1)^2+4u^2}.$$

Let $w_n=8/(\pi^2(2n+1)^2)$ and
$a_n=1/(4\pi^2(2n+1)^2)$. These weights sum to one.
Mixing the laws of $a_nU^2$ with weights $w_n$, where $U$ has density
$e^{-u}$ on $u>0$, defines a probability law $P$ on $(0,\infty)$.
Termwise integration and the substitution $u=xt$ give

$$r(x)=\frac{x}{8}S_P(x^2),\qquad
S_M(z)=\int\frac1{z+v}\,dM(v).$$

The moments of $P$ are $1/24$, $1/80$ and $17/1792$.
The size-biased probability law $dQ(v)=24v\,dP(v)$ has mean $3/10$.
The variances of $P,Q$ are respectively $31/2880$ and $771/5600$.

For a positive probability law with mean $a$ and finite positive variance
$\sigma^2$, centering gives

$$G_M(z)=\frac{z^3}{\sigma^2}\left(S_M(z)-\frac1{z+a}\right)
=\frac1{\sigma^2}\int(v-a)^2
\left(\frac z{z+a}\right)^2\frac z{z+v}\,dM(v).$$

The kernel is strictly increasing in $z>0$, and positive variance
prevents its nonnegative multiplier from vanishing almost everywhere.
Thus $G_M$ is strictly increasing.
For any positive probability law not concentrated at one point,
$H_M(z)=1/S_M(z)-z$ is also strictly increasing, without moment assumptions.
An exact squared remainder for the two resolvents proves strictness:
equality would force $v$ to be constant almost everywhere.

With $m=1/24$ and $z=x^2$, size biasing gives
$zS_P(z)=1-mS_Q(z)$. Exact algebra identifies

$$\theta(x)=-G_P(x^2),\qquad \chi(x)=G_Q(x^2),\qquad
\mu(x)=H_Q(x^2)-m.$$

Both transforms are strictly positive. Together with the size-bias
identity and $r(x)=xS_P(x^2)/8$, this proves both nonvanishing assertions.
Squaring is strictly increasing on positive reals, giving all three comparisons.

## Falsifier

A real pair $0<x<y$ violating any of the three strict comparisons,
or a positive $x$ at which either specified reciprocal denominator vanishes,
would contradict the assertion. The complete positive ray is included.

## Evidence

`D5/S3/Analytic/WallisRemainder/Result.result` proves exactly `Defs.claim`.
Its principal dependencies are `Measure.r_eq_stieltjes`,
`Stieltjes.strictMonoOn_jensenRemainder` and
`Stieltjes.strictMonoOn_inv_stieltjes_sub`, with the positive-support,
size-bias and moment theorems of `Measure`.
The analytic representation uses `Laplace.r_eq_laplace` and
`Measure.tanh_div_hasSum`. The axiom closure of `Result.result` is
`{propext, Classical.choice, Quot.sound}`.

The proof route was derived with the assistance of the ChatGPT Pro model.
The source proves continuity and boundedness of the remainders in
Theorems 2.1–2.3 and leaves their monotonicity open in Section 4;
Section 5 restates the question. No answer was found in the bounded
literature scope covering the DOI, title, authors and the constants
23040 and 358400. Citation indexes were not checked exhaustively;
this scope does not establish priority or exhaustive literature coverage.

## Triage

- **PROVED.** On $(0,\infty)$, $\mu$ and $\chi$ are strictly increasing
  and $\theta$ is strictly decreasing, with $\ln B(x)\ne0$ and the
  inner bracket of $\mu$ nonzero, by `Result.result`.
- **PROVED.** For $x>0$,
  $r(x)=-\ln B(x)=\int_0^\infty e^{-xt}\tanh(t/4)/(2t)\,dt$,
  by `Laplace.r_eq_laplace`.
- **PROVED.** For every probability measure on $(0,\infty)$ not
  concentrated at a point, $z\mapsto1/S(z)-z$ is strictly increasing,
  by `Stieltjes.strictMonoOn_inv_stieltjes_sub`. With finite positive
  variance and mean $a$, the normalized Jensen remainder
  $z^3(S(z)-1/(z+a))/\sigma^2$ is strictly increasing,
  by `Stieltjes.strictMonoOn_jensenRemainder`.
- **PROVED in prose.** The endpoint limits are $\mu(0+)=0$,
  $\mu(\infty)=31/120$, $\theta(0+)=0$, $\theta(\infty)=-1$,
  $\chi(0+)=0$ and $\chi(\infty)=1$; consequently the images are
  $(0,31/120)$, $(-1,0)$ and $(0,1)$ respectively. At zero, continuity
  and positivity of Gamma at $1/2$ and $1$ give
  $\ln B(x)=\frac12\ln x+O(1)$, which yields all three zero limits
  directly from their definitions. At infinity, dominated convergence
  in the centered formula for $G_M$ above gives $G_P,G_Q\to1$.
  Also
  $H_Q(z)=\mathbb E_Q[zV/(z+V)]/\mathbb E_Q[z/(z+V)]\to3/10$,
  by domination by $V$ and $1$, respectively. Thus
  $H_Q(z)-1/24\to31/120$. The defining expressions are continuous
  on the positive ray because their denominators are nonzero;
  the intermediate value theorem and strict monotonicity give the images.
- **OPEN.** Complete monotonicity properties of endpoint differences
  or derivatives of these remainders are not established here.
  With the standard convention that a completely monotone function is
  nonnegative and nonincreasing, the three remainders themselves cannot
  all have that property: $\mu,\chi$ increase strictly and $\theta<0$.

## ASSUMED-UNVERIFIED

Exhaustive literature coverage, citation-index completeness and priority
are unverified. No claim of exhaustive absence of another solution follows
from the bounded literature scope.
