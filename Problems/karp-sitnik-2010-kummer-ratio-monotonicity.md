---
slug: karp-sitnik-2010-kummer-ratio-monotonicity
bibkey: karpsitnik2010logconvexity
doi: 10.1016/j.jmaa.2009.10.057
triage: theorem
motivation_gids:
  - D5/S3/Analytic/KummerRatio/Result.result
url: https://arxiv.org/abs/0902.3073
---

# Monotonicity and exact ranges of the shifted Kummer ratio

## Problem

Karp and Sitnik, *Log-convexity and log-concavity of hypergeometric-like
functions*, arXiv:0902.3073v1, the unnumbered Conjecture after Theorem 4:

> Conjecture. The ratio in the middle of (10) is monotone decreasing from (0, ∞) onto (1, A), where A is the left-hand side of (10); the ratio in the middle of (11) is monotone increasing from (−∞, 0) onto (B, 1), where B is the left-hand side of (11).

Write $M(s;c;x)={}_1F_1(s;c;x)$ and

$$R(x)=\frac{M(b+\delta;c;x)M(a;c;x)}
 {M(a+\delta;c;x)M(b;c;x)}.$$

Theorem 4 assumes $\delta>0$ throughout. Its inequality (10), for
$b>a>0$ and $c,x>0$, is

$$\frac{\Gamma(a+\delta)\Gamma(b)}
 {\Gamma(b+\delta)\Gamma(a)}<R(x)<1.$$

Its inequality (11), for $a<b<c-\delta$ and $c>0>x$, is

$$\frac{\Gamma(c-a-\delta)\Gamma(c-b)}
 {\Gamma(c-b-\delta)\Gamma(c-a)}<R(x)<1.$$

The printed “onto (1, A)” names the endpoints in the order
$x\to0^+$, $x\to+\infty$. The formal image is the open interval $(A,1)$.
On the negative ray the image is $(B,1)$, with the displayed Gamma quotient
as $B$.

### Formal reading

All Lean names below have prefix `D5.S3.Analytic.KummerRatio`.

| Source object | Lean name | Correspondence |
| --- | --- | --- |
| $(s)_n/((c)_n n!)$ | `Defs.kummerCoeff` | Ascending Pochhammer evaluations divided by the lower Pochhammer evaluation and factorial. |
| $M(s;c;x)={}_1F_1(s;c;x)$ | `Defs.kummer` | The infinite real series with these coefficients. |
| Middle ratio in (10) and (11) | `Defs.ratio` | Exactly $M(b+\delta;c;x)M(a;c;x)/(M(a+\delta;c;x)M(b;c;x))$. |
| Positive-ray clause | `Defs.claim`, `Result.result` | Every $c,\delta>0$ and $0<a<b$; strict decrease and image $(A,1)$. |
| Negative-ray clause | `Defs.claim`, `Result.result` | Every $c,\delta>0$ and $a<b<c-\delta$; strict increase and image $(B,1)$. |

## Motivation

The settling declaration is `D5/S3/Analytic/KummerRatio/Result.result`.
The source note is `D5/L/Asymptotics/karpsitnik2010logconvexity`.
The conclusion determines the full variation of the ratio in the real
argument, including the sharp Gamma endpoints in both parameter regimes.

## Gap

Status: **Proved** for both clauses with the stated quantifiers.
Both monotonicity conclusions are strict and both images are exact.
Ratios with more than one upper parameter are outside this claim.

## Route

For $s,c>0$, the entire defining series solves
$xy_s''+(c-x)y_s'-s y_s=0$ and satisfies $y_s(x)\ge1$ for $x\ge0$.
The logarithmic derivative $h_s=y_s'/y_s$ satisfies

$$h_s'=s/x+(1-c/x)h_s-h_s^2.$$

For $v>u>0$, the weight
$\mu_{u,v}=x^c e^{-x}y_u y_v$ gives

$$[\mu_{u,v}(h_v-h_u)]'=(v-u)\mu_{u,v}/x>0.$$

The weighted difference extends continuously to zero with value zero,
so $h_v>h_u$ for $x>0$. Put $w_s=h_{s+\delta}-h_s$ and
$S_s=h_{s+\delta}+h_s$. A second identity is

$$[\mu_{b,b+\delta}(w_b-w_a)]'
=\mu_{b,b+\delta}(S_a-S_b)w_a<0.$$

Its value at zero is again zero. Thus $w_b<w_a$ and
$R'/R=w_b-w_a<0$.

For $0<s<c$, the beta integral represents $M(s;c;x)$. Endpoint
concentration gives $e^{-x}x^{c-s}M(s;c;x)\to\Gamma(c)/\Gamma(s)$.
The contiguous relation extends this limit to every $s,c>0$.
The four limits in the ratio give $A$. Continuity, $M(s;c;0)=1$,
strict decrease and the intermediate value theorem give the image $(A,1)$.
Kummer's transformation gives
$R(a,b,c,\delta,x)=R(c-b-\delta,c-a-\delta,c,\delta,-x)$;
the positive-ray result therefore gives the negative-ray result and $B$.

The comparison uses positivity on the closed positive ray, continuity of
the solution and its first derivative there, and two derivatives satisfying
the equation on the positive ray. The value at zero can be any positive
normalization: the vanishing factor $x^c$ provides both zero boundary
values in the weighted identities.

## Falsifier

An admissible pair $0<x_1<x_2$ with $R(x_1)\le R(x_2)$, or an admissible
pair $x_1<x_2<0$ with $R(x_1)\ge R(x_2)$, would contradict the respective
strict monotonicity clause. A ratio value outside the asserted interval,
or an interior value missing from the image, would contradict the exact
image clause of `Result.result`.

## Evidence

`D5/S3/Analytic/KummerRatio/Result.result` proves exactly `Defs.claim`.
Its principal dependencies are `Comparison.ratio_strictAntiOn`,
`Asymptotics.tendsto_kummer_atTop`, `Transform.kummer_transform`,
`Series.continuous_kummer`, `Series.one_le_kummer`, and `Series.kummer_zero`.
The general ODE comparison is `Comparison.solution_ratio_strictAntiOn`;
the integral representation is `BetaIntegral.kummer_eq_betaIntegral`.
The accepted axiom closure of the result is contained in
`{propext, Classical.choice, Quot.sound}`.

The proof route was derived with the assistance of the ChatGPT Pro model.
Mehrez–Sitnik, arXiv:1410.6120, *Analysis* 36 (2016), settles the related
lower-parameter ratio
${}_1F_1(a;b-c;x){}_1F_1(a;b+c;x)/{}_1F_1(a;b;x)^2$.
That is a different function. No settlement of the present conjecture was
found in the bounded scope consisting of queries combining Karp, Sitnik,
Kalmykov, Kummer ratio monotonicity and upper parameters; Karp–Zhang
arXiv:2305.09029; Segura arXiv:2408.05573, Section 5; Derbazi
arXiv:2607.02511; and the repository's D5, Library, Problems and
pull-request entries for Kummer, Karp, Sitnik and confluent hypergeometric
functions. The existing Karp entry concerns polynomial truncations.
This scope does not provide exhaustive citation-index or priority coverage.

## Triage

- **PROVED.** The logarithmic-derivative ordering $h_v>h_u$ for
  $v>u>0$ and the finite-increment comparison
  $h_{b+\delta}-h_b<h_{a+\delta}-h_a$ hold for $x>0$, under the regular
  positive ODE-family hypotheses in Route. They are the internal comparison
  steps used by `Comparison.solution_ratio_strictAntiOn`.
- **PROVED.** The beta-integral representation holds for $0<s<c$.
  The endpoint asymptotic
  $e^{-x}x^{c-s}M(s;c;x)\to\Gamma(c)/\Gamma(s)$ holds for all $s,c>0$,
  by `BetaIntegral.kummer_eq_betaIntegral` and
  `Asymptotics.tendsto_kummer_atTop`.
- **PROVED in prose.** The comparison argument applies to any family of
  positive solutions of $xy''+(c-x)y'-sy=0$ with $y_s(0)=1$ and the
  regularity in Route, so it covers the ratios
  $y_{b+\delta}y_a/(y_{a+\delta}y_b)$ for that ODE family. The Lean theorem
  `Comparison.solution_ratio_strictAntiOn` allows arbitrary positive
  normalizations at zero and hence includes this normalized case.
- **OPEN.** The analogous monotonicity in $x$ for the generalized
  hypergeometric ratio with $p>1$ upper parameters is not settled here.

## ASSUMED-UNVERIFIED

Exhaustive literature coverage, priority and citation-index completeness
are unverified. The full texts of the Sablica–Hornik papers in
*Mathematics of Computation* 91 (2022) and *Journal of Mathematical
Analysis and Applications* 537 (2024), concerning contiguous Kummer ratio
bounds, were not read. No conclusion about their coverage of this
conjecture is asserted.
