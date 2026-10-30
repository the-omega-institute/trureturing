---
slug: baricz-mehrez-2018-bessel-redheffer-lower-bound
bibkey: bariczmehrez2018redheffer
doi: 10.1007/s00010-018-0545-8
triage: theorem
motivation_gids:
  - D5/S3/Analytic/BesselRedheffer/Result.result
url: https://arxiv.org/abs/1701.08446
---

# Refutation of the normalized Bessel Redheffer lower bound

## Problem

Á. Baricz and K. Mehrez, *Redheffer type bounds for Bessel and modified
Bessel functions of the first kind*, arXiv:1701.08446v1, §3,
Conjecture 1, inequality (3.2):

> If ν > −1 and |x| < j_{ν,1}, then the following inequalities are valid (j_{ν,1}²/(j_{ν,1}² − x²))^{ϑ_ν} ≤ 𝒥_{ν+1}(x)/𝒥_ν(x) ≤ (j_{ν,1}²/(j_{ν,1}² − x²))^{η_ν}, where ϑ_ν = j_{ν,1}²/(4(ν+1)(ν+2)) and η_ν = 1 are the best possible constants.

The source states the left-hand inequality as the conjecture; the
right-hand inequality is a known result. The source proves the lower
bound in the case $\nu=-1/2$. Only the lower bound is refuted here.

### Formal reading

All Lean names below have prefix `D5.S3.Analytic.BesselRedheffer`.

| Source object | Lean name | Correspondence |
| --- | --- | --- |
| $\mathcal J_\nu(x)$ | `Defs.nbessel` | The real sum $\sum_{k\ge0}(-x^2/4)^k/[k!(\nu+1)_k]$ with ascending Pochhammer evaluations. |
| $j_{\nu,1}$ | `Defs.firstZero` | The infimum of $\{x>0:\mathcal J_\nu(x)=0\}$; existence, positivity and attainment are proved for $\nu\ge30$. |
| $\vartheta_\nu$ | Exponent in `Defs.claim` | Exactly $j_{\nu,1}^2/[4(\nu+1)(\nu+2)]$, using the real power. |
| Left-hand inequality of (3.2) | `Defs.claim` | Every real $\nu>-1$ and every real $x$ with $|x|<j_{\nu,1}$. |
| Strict violations | `Result.failure_family` | For every real $\nu\ge30$, some $0<x<j_{\nu,1}$ has the ratio strictly below the proposed lower bound. |
| Universal refutation | `Result.result` | Exactly $\neg\,\texttt{Defs.claim}$. |

## Motivation

The settling declaration is `D5/S3/Analytic/BesselRedheffer/Result.result`.
The source note is `D5/L/Asymptotics/bariczmehrez2018redheffer`.
The proposed exponent makes the quadratic terms at the origin equal.
The quartic terms determine whether this local agreement can extend to
a valid lower bound.

## Gap

Status: **Refuted**. For every real $\nu\ge30$ the lower bound fails
at all sufficiently small positive arguments. In particular, the order
$\nu=30$ contradicts the universal claim. The upper bound in (3.2)
and the exact range of orders satisfying the lower bound are not settled
by this refutation.

## Route

Put $b=\nu+1$, $j=j_{\nu,1}$ and $J=j^2$. The normalized series is entire,
equals one at zero, and satisfies

$$F_b''(x)+\frac{2b-1}{x}F_b'(x)+F_b(x)=0\quad(x>0).$$

For $\nu\ge30$ a positive first zero exists, is attained, and satisfies

$$J\le U(\nu):=\frac65(\nu+1)(\nu+7).$$

With $y(r)=F_b(zr)$, $w(r)=r^{2b-1}$, $h=y'/y$ and
$u(r)=(1-r^2)^3$, positivity on $[0,z]$ gives

$$0\le\int_0^1w(u'-hu)^2=E_b-z^2D_b,$$

$$D_b=\int_0^1r^{2b-1}(1-r^2)^6\,dr,\qquad
E_b=36\int_0^1r^{2b+1}(1-r^2)^4\,dr
=\frac65b(b+6)D_b.$$

The boundary term vanishes and $D_b>0$. This bounds every positive
initial interval, supplies a positive zero, and gives the bound for its
infimum by continuity.

The common quadratic coefficient of the ratio $R$ and proposed bound $L$
is $r_2=1/[4b(b+1)]$. Their quartic coefficients are

$$R_4=\frac1{8b^2(b+1)(b+2)},\qquad
L_4=\frac1{32b^2(b+1)^2}+\frac1{8b(b+1)J}.$$

Thus

$$L_4>R_4\iff J<T(\nu),\qquad
T(\nu)=\frac{4(\nu+1)(\nu+2)(\nu+3)}{3\nu+5}.$$

For $b\ge31$, $U(\nu)<T(\nu)$ reduces to
$b^2-30b-16>0$. For nonnegative $\nu$ and $|x|\le1/2$, the explicit
ratio error satisfies

$$|R(x)-1-r_2x^2-R_4x^4|\le16x^6.$$

The positive binomial series gives $L(x)\ge1+r_2x^2+L_4x^4$ for
$0\le x<j$. Writing $\Delta=L_4-R_4>0$, every

$$0<x<\min\{j,1/2,\Delta/32\}$$

therefore satisfies $R(x)<L(x)$. This is a positive interval for every
$\nu\ge30$.

## Falsifier

A single admissible order and argument giving the strict reversed
inequality refutes the conjectured lower bound. `Result.result` uses
order $30$. An order $\nu\ge30$ for which arbitrarily small positive
arguments satisfy the proposed lower bound would contradict the stronger
local family conclusion. An error in the energy identity, the moment
evaluation or the quartic error estimate would invalidate that route
without establishing the conjecture.

## Evidence

`D5/S3/Analytic/BesselRedheffer/Result.result` proves exactly
`result : ¬ claim`. Its principal dependencies are `Result.failure_family`,
`Expansion.failure_of_energy_bound`, `FirstZero.firstZero_pos` and
`FirstZero.firstZero_sq_le`. The first-zero argument also proves
`FirstZero.nbessel_firstZero` and uses `Series.nbessel_zero`,
`Series.continuous_nbessel`, the shifted-order derivative identities and
`Series.nbessel_ode`. The axiom closure of the result and the two public
failure theorems is exactly `{propext, Classical.choice, Quot.sound}`.
The all-sufficiently-small conclusion is the application of
`Expansion.failure_of_energy_bound` to the actual first zero; the named
`Result.failure_family` selects one point in that interval.

The refutation route was derived with the assistance of the ChatGPT Pro model.
No settlement was found in the bounded literature scope consisting of
queries combining the title, the authors, Conjecture 1, counterexample
and disproof; the citing discussions in *Mathematics* 11 (2023), 379,
and Aktaş–Baricz–Singh, *Ramanujan Journal* (2020); and the repository's
D5, Library, Problems and pull-request entries for Redheffer, Baricz and
Mehrez. The cited discussions did not report a settlement. This scope
does not establish exhaustive citation-index coverage or priority.

## Triage

- **PROVED.** For every real $\nu\ge30$, the attained first positive zero
  satisfies $j_{\nu,1}^2\le(6/5)(\nu+1)(\nu+7)$, by
  `FirstZero.firstZero_sq_le`.
- **PROVED.** For every real $\nu\ge30$, the lower bound fails at all
  sufficiently small $x>0$, by the fourth-order comparison in
  `Expansion.failure_of_energy_bound` and the first-zero estimates.
- **COMPUTED.** With 60-digit series evaluation and bisection for
  $j_{\nu,1}$, the lower bound holds at all sampled points
  $x/j_{\nu,1}\in\{0.01,0.02,\ldots,0.98\}$ for
  $\nu\in\{-0.5,0,2,8,10,12,14,16\}$ and fails for $\nu=18$
  at $x/j_{\nu,1}=0.06$, and for $\nu\in\{20,29,30,40,60\}$.
  These computations are separate from the Lean proof.
- **PROVED in prose.** For $\nu>-1$, near $x=0$ the lower bound holds
  if $j_{\nu,1}^2>T(\nu)$ and fails if $j_{\nu,1}^2<T(\nu)$, where
  $T(\nu)=4(\nu+1)(\nu+2)(\nu+3)/(3\nu+5)$ is the threshold from the
  quartic coefficients. Indeed, the analytic expansions give
  $L(x)-R(x)=(L_4-R_4)x^4+O(x^6)$ with positive denominators, so its
  sign for sufficiently small nonzero $x$ is the sign of
  $T(\nu)-j_{\nu,1}^2$. Equality at the threshold requires higher terms.
- **OPEN.** The exact set of $\nu>-1$ for which the lower bound holds
  on the whole interval remains undetermined. The sampled behavior changes
  between orders 16 and 18. The computations do not prove a
  unique transition or validity at unsampled arguments.

## ASSUMED-UNVERIFIED

The full texts of Mehrez, *Journal of Computational and Applied
Mathematics* (2019), DOI 10.1016/j.cam.2019.05.025, and Mao–Tian
(2025), DOI 10.1080/10652469.2025.2571692, were not read. No conclusion
about their coverage of the conjecture is asserted. Exhaustive
literature coverage, citation-index completeness and priority are
unverified. The formal first-zero existence and attainment results cover
$\nu\ge30$; their classical extension to every $\nu>-1$ is not proved
by these modules.
