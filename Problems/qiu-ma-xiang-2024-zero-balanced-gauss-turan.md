---
slug: qiu-ma-xiang-2024-zero-balanced-gauss-turan
bibkey: qiumaxiang2024turan
doi: 10.48550/arXiv.2408.15723
triage: theorem
motivation_gids:
  - D5/S3/Analytic/GaussZeroBalanced/Result.result
url: https://arxiv.org/abs/2408.15723
---

# Sharp parameter thresholds for the zero-balanced Gauss quotient

## Problem

Qiu, Ma and Xiang, *Turán-type inequalities for Gaussian hypergeometric
functions, and Baricz's conjecture*, arXiv:2408.15723v1, §6,
Conjecture 6.2:

> The inequality (1.6) holds for all r ∈ (0, 1) and a ∈ (0, ∞) if and only if b ∈ (0, √(a(a+1))], and the inequality (1.7) holds for all r ∈ (0, 1) if and only if a ∈ [3/7, 1).

Write $F(a,b;c;r)={}_2F_1(a,b;c;r)$. Inequality (1.6) is

$$\frac{\partial}{\partial b}
\left[\frac{F(a+1,b+1;a+b+1;r)}{F(a,b;a+b;r)}\right]<0,$$

and inequality (1.7) is

$$\frac{F(a+1,2-a;2;r)}{F(a,1-a;1;r)}
>\frac{F(a+1,5/2-a;5/2;r)}{F(a,3/2-a;3/2;r)}.$$

The first classification is read pointwise in the positive parameters:
for each $a,b>0$, the derivative is negative at every $r\in(0,1)$
if and only if $b\le\sqrt{a(a+1)}$.
The second classification assumes $0<a<1$.
This corrects Baricz's 2007 Conjecture A, which the same paper refutes
as an unrestricted statement.

### Formal reading

All Lean names below have prefix `D5.S3.Analytic.GaussZeroBalanced`.

| Source object | Lean name | Correspondence |
| --- | --- | --- |
| $F(a,b;c;x)={}_2F_1(a,b;c;x)$ | `Defs.gauss` | Mathlib's real `ordinaryHypergeometric`, with its canonical series. |
| Quotient in (1.6) | `Defs.quot` | Exactly $F(a+1,b+1;a+b+1;x)/F(a,b;a+b;x)$. |
| Contiguous quotient $f$ | `Defs.f` | Exactly $F(a,b;a+b+1;x)/F(a,b;a+b;x)$. |
| Inequality (1.7) | `Defs.ineq17` | The displayed strict shifted-parameter quotient comparison. |
| First clause | `Defs.claim`, `ParamDeriv.clause1` | Every $a,b>0$; negativity of `deriv (fun β => quot a β x) b` for every $0<x<1$ iff $b\le\sqrt{a(a+1)}$. |
| Second clause | `Defs.claim`, `Comparison.clause2` | Every $0<a<1$; (1.7) for every $0<r<1$ iff $3/7\le a$. |
| Both clauses | `Result.result` | The conjunction `Defs.claim`, without additional hypotheses. |

## Motivation

The settling declaration is `D5/S3/Analytic/GaussZeroBalanced/Result.result`.
The source note is `D5/L/Asymptotics/qiumaxiang2024turan`.
The result gives the exact parameter range for strict derivative negativity
and the exact threshold for the shifted-parameter comparison.

## Gap

Status: **Proved** for both clauses with the stated quantifiers.
The threshold equalities are included, and the inequalities in the
argument remain strict. The lower parameter is constrained by zero balance;
the classification for independent lower parameter is outside this claim.

## Route

Put $c=a+b$, $t=x/(1-x)$, $q=ab/(c(c+1))$ and
$f=F(a,b;c+1;x)/F(a,b;c;x)$. Positive series coefficients give
$0<f<1$ on $(0,1)$ and $f(0)=1$. The contiguous identities give
$Q=f/(1-x)$ and

$$xf'=c(1-f)-(ab/c)tf^2.$$

For $E=qtf^2+f-1$, the differential identity is

$$xE'+c(1+2qtf)E=qt^2f^2(1-2qf)>0.$$

Continuity at zero and the singular endpoint comparison imply $E>0$,
hence $(1-f)/(tf^2)<q$. Termwise parameter differentiation uses locally
uniform summable bounds for the coefficient derivatives. The same bounds
with an additional index factor justify both mixed derivative orders.
For $h=\partial_b f$, the variational equation is

$$xh'+(c+2(ab/c)tf)h=(1-f)-(a^2/c^2)tf^2.$$

If $b^2\le a(a+1)$, then $q\le a^2/c^2$, so the certificate makes
the forcing strictly negative and singular comparison gives $h<0$.
Conversely, $h(0)=0$ and

$$h'(0)=\frac{a\bigl(b^2-a(a+1)\bigr)}{(a+b)^2(a+b+1)^2}.$$

If $h<0$ throughout $(0,1)$, its right derivative at zero is nonpositive,
which forces the threshold. Division by $1-x>0$ transfers the result to $Q$.

Subtracting the Riccati equations at $0<b_1<b_2$ gives a linear equation
for $w=f(a,b_1,x)-f(a,b_2,x)$. Its forcing is

$$ (b_2-b_1)\left[
\frac{a^2tf(a,b_1,x)^2}{(a+b_1)(a+b_2)}-(1-f(a,b_1,x))\right].$$

The certificate makes this strictly positive when $b_1b_2\le a(a+1)$;
the initial slope of $w$ supplies necessity. Substituting
$b_1=1-a$, $b_2=3/2-a$ gives
$a(a+1)-b_1b_2=(7a-3)/2$, establishing the second threshold.

## Falsifier

An admissible $a,b>0$ with $b\le\sqrt{a(a+1)}$ and an argument
$0<x<1$ where $\partial_b Q\ge0$, or a parameter above that threshold
whose derivative is negative throughout $(0,1)$, would contradict the
first clause. An admissible $a\ge3/7$ and $0<r<1$ violating (1.7),
or an admissible $a<3/7$ satisfying (1.7) throughout $(0,1)$, would
contradict the second clause.

## Evidence

`D5/S3/Analytic/GaussZeroBalanced/Result.result` proves exactly `Defs.claim`.
Its principal dependencies are `ParamDeriv.clause1` and `Comparison.clause2`.
The analytic steps are `Series.riccati`, `Series.quot_eq`,
`Comparison.singular_comparison`, `Comparison.certificate`,
`Comparison.comparison_iff`, `Comparison.comparison_iff_quot`,
`ParamDeriv.hasDerivAt_gauss_param`, `ParamDeriv.hasDerivAt_f_mixed`,
`ParamDeriv.hasDerivAt_f_param_zero` and `ParamDeriv.parameter_equation`.
The accepted axiom closure of the result is contained in
`{propext, Classical.choice, Quot.sound}`.

The proof route was derived with the assistance of the ChatGPT Pro model.
Derbazi, arXiv:2607.02511, §3.4, proves the necessity direction:
(1.6) fails at sufficiently small positive $r$ when $b>\sqrt{a(a+1)}$.
No other settlement was found in the bounded scope consisting of
Yin–Mi–Xu (2018), Ma–He–Zhong (2025), Dai–Sang (2025),
arXiv:2607.05538 on Bessel ratios, Formal Conjectures, and the repository's
D5, Library, Problems and pull-request entries for Baricz, Qiu and the
zero-balanced quotient. The cited works on other hypergeometric and
Bessel inequalities do not settle these two classifications.
This scope does not provide exhaustive citation-index or priority coverage.

## Triage

- **PROVED.** For $a,b>0$ and $0<x<1$, the certificate bound is
  $(1-f)/(tf^2)<ab/((a+b)(a+b+1))$, by `Comparison.certificate`.
- **PROVED.** For $a>0$ and $0<b_1<b_2$, the quotient
  $F(a,b;a+b+1;x)/F(a,b;a+b;x)$ at $b_1$ exceeds its value at $b_2$
  throughout $(0,1)$ if and only if $b_1b_2\le a(a+1)$,
  by `D5.S3.Analytic.GaussZeroBalanced.Comparison.comparison_iff`.
- **PROVED in prose.** The comparison remains strict in the boundary
  cases $b^2=a(a+1)$ and $b_1b_2=a(a+1)$, because the forcing term
  of the comparison equation for $-h$ and for $w$, respectively,
  is strictly positive by the certificate.
- **OPEN.** The analogous classification for the non-zero-balanced
  quotient $F(a+1,b+1;c+1;x)/F(a,b;c;x)$ with $c\ne a+b$ is not
  settled here.

## ASSUMED-UNVERIFIED

Exhaustive literature coverage, priority and citation-index completeness
are unverified. The bounded literature scope does not imply that no
other settlement exists.
