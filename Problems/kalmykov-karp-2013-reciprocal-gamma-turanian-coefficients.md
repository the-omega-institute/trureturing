---
slug: kalmykov-karp-2013-reciprocal-gamma-turanian-coefficients
bibkey: kalmykovkarp2013logconcavity
doi: 10.1080/10652469.2013.764874
triage: theorem
motivation_gids:
  - D5/S3/Analytic/ReciprocalGammaTuran/Result.result
url: https://arxiv.org/abs/1206.4814
---

# Refutation of reciprocal Gamma coefficient positivity

## Problem

S. I. Kalmykov and D. B. Karp, *Log-concavity for series in reciprocal
gamma functions and applications*, arXiv:1206.4814v1, Conjecture 1:

> Under hypotheses of Theorem 2 the function µ → g(µ, x) is log-concave on (0, ∞) for each fixed x ≥ 0. Moreover, the function x → g(µ + α, x)g(µ + β, x) − g(µ, x)g(µ + α + β, x) has positive power series coefficients for µ ≥ −1 and µ + α ≥ 0, µ + β ≥ 0, where α, β > 0.

Theorem 2's sequence hypotheses are nontriviality, nonnegativity,
log-concavity $g_{n-1}g_{n+1}\le g_n^2$ for $n\ge1$, and no internal
zeros. Equation (20) is

$$g(\mu,x)=\sum_{n=0}^{\infty}\frac{g_n x^n}{\Gamma(n+\mu)},$$

where reciprocal Gamma is zero at its poles. Only the “Moreover” clause
is refuted; the first assertion is not addressed.

### Formal reading

All Lean names below have prefix `D5.S3.Analytic.ReciprocalGammaTuran`.

| Source object | Lean name | Correspondence |
| --- | --- | --- |
| $1/\Gamma(s)$ | `Defs.rgamma` | Inverse real Gamma, zero at nonpositive integers. |
| Theorem 2's sequence hypotheses | `Defs.AdmissibleSeq` | Nontrivial, nonnegative, log-concave, without internal zeros. |
| Equation (20)'s formal series | `Series.formalSeries` | Degree $n$ coefficient $g_n/\Gamma(n+\mu)$, with no factorial weight. |
| Degree $m$ Turanian coefficient | `Defs.turanCoeff`, `Series.coeff_mul` | Exact finite Cauchy sum over $0\le k\le m$. |
| Moreover clause | `Defs.claim` | Every admissible sequence and all real shifts in the printed range, at every natural degree. |
| Boundary failure | `Boundary.d_two_neg` | For every $0<t<1$, degree two is negative at $(-t,t,t)$. |
| Interior failure | `Interior.interior_failure` | Positive shifted parameters and a negative second coefficient. |
| Refutation | `Result.result` | Exactly $\neg\,\texttt{Defs.claim}$. |

## Motivation

The settling declaration is
`D5/S3/Analytic/ReciprocalGammaTuran/Result.result`.
The source note is `D5/L/Asymptotics/kalmykovkarp2013logconcavity`.
The constant unit sequence satisfies every sequence hypothesis. Its
boundary shifts expose a negative coefficient, and continuity shows
that this failure persists strictly inside the permitted range.

## Gap

Status: **Refuted**. The second coefficient fails for the unit sequence
at every boundary triple $(-t,t,t)$ with $0<t<1$, and also at strictly
interior parameters. The first assertion on log-concavity for positive
parameters is not addressed. Positivity of every coefficient throughout
the principal range $\mu\ge0$ is not settled here.

## Route

Write $F_b(x)=\sum_{n\ge0}x^n/\Gamma(n+b)$ and
$D_t(x)=F_0(x)^2-F_{-t}(x)F_t(x)=\sum_m d_m x^m$.
The finite Cauchy identity gives

$$d_2=1-\frac{1+t^2}{t(1-t^2)\Gamma(t)\Gamma(1-t)}.$$

The formal proof uses Euler reflection and the strict bound

$$\sin(\pi t)>\frac{\pi t(1-t^2)}{1+t^2}\qquad(0<t<1).$$

For $u=t^2$, the finite Euler product is at least
$(1-u)(1-u/4)(1+u/(n+2))/(1+u/2)$. The induction follows from

$$(1+u/a)(1-u/(a+1)^2)-(1+u/(a+1))
=\frac{u(1-u)}{a(a+1)^2}\ge0.$$

Its limit gives the displayed strict sine bound, hence $d_2<0$.
The entire reciprocal Gamma function makes the second Cauchy
coefficient jointly continuous. Increasing $\mu$ by a sufficiently small
positive amount preserves negativity and makes both shifted parameters
strictly positive. The unit sequence then contradicts universal positivity.

The all-degree formula has the following separate prose proof. Put
$C=1/(\Gamma(t)\Gamma(1-t))$, $f(v)=v^{1-t}-v^{1+t}$ and
$A(s)=\int_0^1v^{s-1}/(1+v)\,dv$ for $s>0$.
Splitting the beta integral on $(0,\infty)$ at one and substituting
$v=1/u$ in its tail gives
$A(t)+A(1-t)=\Gamma(t)\Gamma(1-t)$.
Adding integrands gives $A(s)+A(s+1)=1/s$.
Consequently

$$I_2:=A(2-t)-A(2+t)
=\frac{1+t^2}{t(1-t^2)}-\Gamma(t)\Gamma(1-t),
\qquad d_2=-C I_2.$$

The eventual ratio of successive terms of $F_b$ is $x/(n+b)$,
so its radius is infinite and termwise differentiation is valid.
Gamma recurrence, applied coefficientwise, gives
$xF_b'=(x+1-b)F_b+(b-1)/\Gamma(b)$ and
$xD_t'=2(x+1)D_t+R_t$. Thus, for $m\ge3$,

$$(m-2)d_m=2d_{m-1}+r_m,\quad
r_m=\frac{t+1}{\Gamma(-t)\Gamma(m+t)}
+\frac{1-t}{\Gamma(t)\Gamma(m-t)}.$$

The beta integral and integration by parts, using $f(0)=f(1)=0$, yield

$$r_m=\frac{C}{(m-2)!}\int_0^1 f'(v)(1-v)^{m-2}\,dv
=\frac{C}{(m-3)!}\int_0^1 f(v)(1-v)^{m-3}\,dv.$$

For $I_m=\int_0^1 f(v)(1-v)^{m-2}/(1+v)\,dv$, the identity
$(1-v)/(1+v)=2/(1+v)-1$ now proves inductively
$d_m=-C I_m/(m-2)!$. Every integral is finite and strictly positive:
$f(v)>0$ for $0<v<1$ and $0<t<1$. This argument is a prose result;
the Lean proof uses only the second coefficient and continuity.

## Falsifier

A single admissible sequence and admissible parameter triple with a
negative coefficient refutes the universal clause. The unit sequence
and the strictly interior triple supplied by `Interior.interior_failure`
provide such a counterexample. An error in the Gamma evaluation or
strict sine bound would invalidate this route without proving the clause.

## Evidence

`D5/S3/Analytic/ReciprocalGammaTuran/Result.result` has exactly the type
`result : ¬ claim`, with no additional hypotheses. Its principal
dependencies are `Defs.admissible_one`, `Interior.interior_failure`,
`Interior.continuous_turanCoeff_two`, `Boundary.d_two_neg`,
`Series.turanCoeff_one_boundary` and `Series.coeff_mul`.
The boundary argument uses a finite Euler-product lower bound and
Mathlib's reflection and sine-product theorems. The result's axiom
closure is exactly `{propext, Classical.choice, Quot.sound}`.
The coefficient identification is a formal power-series identity;
no separate Lean theorem for convergence of $F_b$ or its differential
recurrence is asserted by these modules.

The refutation route was derived with the assistance of the ChatGPT Pro model.
No settlement of this clause was found in the searched scope:
arXiv:1611.06724 §3 reports numerical counterexamples for a different
numerator-and-denominator shift family with nonnegative parameters;
the 2017 q-gamma paper, Karp–Zhang (2024),
DOI 10.1007/s13540-023-00238-0, Formal Conjectures and conjectures.io
did not supply a settlement of this clause in that scope.
The existing Karp–Zhang quadratic-truncation and Karp–Sitnik Kummer
results concern different statements. This bounded scope does not
establish exhaustive citation-index coverage or priority.

## Triage

- **PROVED.** For $g_n\equiv1$ and every $0<t<1$, the second coefficient
  at $\mu=-t$, $\alpha=\beta=t$ is negative, by `Boundary.d_two_neg`.
- **PROVED.** Failure occurs at parameters strictly inside the range
  $\mu+\alpha>0$, $\mu+\beta>0$, by `Interior.interior_failure`.
- **PROVED in prose.** At the boundary every coefficient of degree $m\ge2$
  is negative:
  $d_m=-\frac{C}{(m-2)!}\int_0^1
  \frac{v^{1-t}-v^{1+t}}{1+v}(1-v)^{m-2}\,dv$,
  where $C=1/(\Gamma(t)\Gamma(1-t))$ and $0<t<1$, as derived above.
- **COMPUTED.** Double-precision coefficients of degrees zero through three
  for $(\mu,\alpha,\beta)=(-0.5,0.6,0.6)$ are
  $0.228,0.097,-0.0018,-0.0144$ after rounding.
  For $\mu\in\{0,0.5\}$ and $\alpha=\beta=0.5$, all computed
  coefficients of degrees zero through twenty are positive.
  These finite computations are separate from the Lean proof.
- **OPEN.** For the unit sequence $g_n\equiv1$, coefficientwise positivity
  for all $\mu\ge0$ and $\alpha,\beta>0$ is left open here. Strict
  positivity cannot hold for every admissible sequence: $g_0=1$ and $g_n=0$
  for $n>0$ is admissible and gives zero coefficients in every positive degree.

## ASSUMED-UNVERIFIED

Exhaustive literature coverage, citation-index completeness and priority
are unverified. The literature scope above is supplied bibliographic
evidence; the external texts were not independently reread here.
The all-degree integral formula is proved in prose, not Lean.
Numerical coefficient signs are finite double-precision observations,
not a proof for the principal range.
