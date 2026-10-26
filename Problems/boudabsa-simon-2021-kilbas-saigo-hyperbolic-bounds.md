---
slug: boudabsa-simon-2021-kilbas-saigo-hyperbolic-bounds
bibkey: boudabsasimon2021kilbassaigo
doi: 10.3390/math9030217
triage: theorem
motivation_gids:
  - D5/S3/Analytic/KilbasSaigo/Result.result
url: https://arxiv.org/abs/2012.05666
---

# Hyperbolic bounds for the Kilbas–Saigo function

## Problem

Boudabsa and Simon, *Some properties of the Kilbas–Saigo function*,
arXiv:2012.05666v1, §4.1, Conjecture 4.5 (Conjecture 4 in the journal):

> For every α ∈ (0, 1], m > 0, l > m − 1/α and x ≥ 0, one has 1/(1 + [Γ(1+α(l−m))/Γ(1+α(l−m+1))] x) ≤ E_{α,m,l}(−x) ≤ 1/(1 + [Γ(1+αl)/Γ(1+α(1+l))] x).

Here

$$E_{\alpha,m,l}(z)=\sum_{n=0}^{\infty}c_nz^n,\qquad
c_n=\prod_{k=0}^{n-1}
\frac{\Gamma(1+\alpha(km+l))}{\Gamma(1+\alpha(km+l+1))},\quad c_0=1.$$

The source records the cases $l=m-1$ and $m=1$ as known.

### Formal reading

All Lean names below have prefix `D5.S3.Analytic.KilbasSaigo`.

| Source object | Lean name | Correspondence |
| --- | --- | --- |
| $c_n$ | `Defs.ksCoeff` | The product over $0\le k<n$, including the empty product at $n=0$. |
| $E_{\alpha,m,l}(z)$ | `Defs.kilbasSaigo` | The real sum of $c_nz^n$; `Series.summable_kilbasSaigo` proves convergence for every real $z$. |
| $a=1+\alpha(l-m)$, $b=\alpha m$, $\phi(s)=\Gamma(a+bs+\alpha)/\Gamma(a+bs)$ | `Series.phi` | The hypotheses imply $a,b>0$ and positivity of every Gamma argument used. |
| $f(x)=E_{\alpha,m,l}(-x)$ | `Series.g` at order zero | `Series.kilbasSaigo_neg_eq_g0` identifies the two series. |
| $g_k=(-1)^kf^{(k)}$ | `Series.g` | `Series.hasDerivAt_g` gives $g_k'=-g_{k+1}$ for every natural $k$. |
| Both bounds and their quantifiers | `Defs.claim`, `Result.result` | All real $\alpha,m,l,x$ with exactly the five displayed hypotheses; both inequalities are non-strict. |

## Motivation

The settling declaration is `D5/S3/Analytic/KilbasSaigo/Result.result`.
The source note is `D5/L/Asymptotics/boudabsasimon2021kilbassaigo`.
The bounds compare an entire special function with two explicit rational
functions throughout the nonnegative argument range.

## Gap

Status: **Proved** for the complete stated range, including $\alpha=1$
and $x=0$. The strict inequality $l>m-1/\alpha$ is retained.
The equality $l=m-1/\alpha$ is outside this statement.

## Route

Put $a=1+\alpha(l-m)>0$, $b=\alpha m>0$ and
$\phi(s)=\Gamma(a+bs+\alpha)/\Gamma(a+bs)$.
The coefficient recurrence is $c_{n+1}=c_n/\phi(n+1)$.
A beta integral and dominated convergence give $1/\phi(n)\to0$.
The ratio criterion gives absolute convergence of every signed derivative
series at every real argument, and uniform local bounds justify differentiation.

For $0<\alpha<1$, set $\lambda=r^b$ and

$$K(r)=\frac{\alpha}{\Gamma(1-\alpha)}
r^{a+\alpha-1}(1-r)^{-1-\alpha},\qquad 0<r<1.$$

The divided difference of $r^q$ regularizes the endpoint at one.
The fundamental theorem of calculus and beta integrals yield, for $q\ge0$,

$$\int_0^1(1-r^q)K(r)\,dr
=\frac{\Gamma(a+q+\alpha)}{\Gamma(a+q)}
-\frac{\Gamma(a+\alpha)}{\Gamma(a)}.$$

The estimate $|1-\lambda^n|\le n(1-\lambda)$ and the absolutely
convergent derivative series justify integration term by term. Thus

$$(\phi(0)+x)f(x)=\phi(0)+\int_0^1[f(\lambda x)-f(x)]K(r)\,dr,$$

$$(\phi(k)+x)g_k(x)=k g_{k-1}(x)
+\int_0^1\lambda^k[g_k(\lambda x)-g_k(x)]K(r)\,dr\quad(k\ge1).$$

A nonpositive minimum on $[0,x]$ makes the integral at that minimum
nonnegative, contradicting the strictly positive forcing.
Induction proves $g_k>0$ for every $k$, hence $f$ is decreasing and convex.
Monotonicity gives $(\phi(0)+x)f(x)\ge\phi(0)$.
Convexity gives

$$0\le f(\lambda x)-f(x)\le(1-\lambda)(1-f(x)).$$

Since $\int_0^1(1-\lambda)K=\phi(1)-\phi(0)$, this yields
$(\phi(1)+x)f(x)\le\phi(1)$.

At $\alpha=1$, $\phi(s)=a+bs$. The coefficient recurrence gives

$$bx f'(x)+(a+x)f(x)=a,\qquad
bx g_k'(x)+(a+bk+x)g_k(x)=k g_{k-1}(x).$$

The left derivative at a positive minimizer and the positive initial
values exclude a nonpositive minimum, successively for all $g_k$.
The ODE, $f'\le0$ and the convex tangent inequality
$f(x)-xf'(x)\le f(0)=1$ give the same two bounds.
Rewriting $\phi(0)$ and $\phi(1)$ gives the two pinned Gamma quotients.

## Falsifier

Real parameters satisfying $0<\alpha\le1$, $m>0$, $l>m-1/\alpha$
and $x\ge0$ for which either displayed inequality fails would contradict
the statement. Equality at $x=0$ and the endpoint $\alpha=1$ are included.

## Evidence

`D5/S3/Analytic/KilbasSaigo/Result.result` proves exactly `Defs.claim`.
Its principal dependency is `Bounds.bounds`, using `Bounds.bounds_one`
and the fractional scaling hierarchy. The analytic dependencies include
`Series.tendsto_inv_phi`, `Series.summable_gCoeff`, `Series.hasDerivAt_g`,
`Bounds.FractionalCertificate.certificate_full`,
`Bounds.ScalingWork.scaling_f`, `Bounds.ScalingWork.scaling_g_succ`,
`Bounds.fractional_system`, `Bounds.ode_one_base` and `Bounds.ode_one_succ`.
The latter analytic helpers are private declarations in `Bounds.lean`.
The axiom closure of `Result.result` is
`{propext, Classical.choice, Quot.sound}`.

The proof route was derived with the assistance of the ChatGPT Pro model.
No settlement was found in the bounded literature scope for Boudabsa,
Simon, Kilbas–Saigo and hyperbolic bounds, including work from 2023–2026.
Koide, Figshare 10.6084/m9.figshare.34328784.v1, concerns the boundary
Conjecture 3.7 at $l=m-1/\alpha$, a different statement.
Karp–Kuznetsov, arXiv:2403.05708, §6, supplies representations;
Beghin–Leonenko–Simon–Vaz, arXiv:2606.03661, cites the source without
settling this conjecture. The repository's mathematical sources,
literature notes, problem dossiers and pull requests supplied no earlier
Kilbas–Saigo settlement in that scope. This bounded scope does not
establish exhaustive citation-index coverage or priority.

## Triage

- **PROVED.** Positivity of $f$ and every signed derivative on $[0,\infty)$
  follows from `Bounds.fractional_system` for $0<\alpha<1$ and
  `Bounds.g_positive_one` for $\alpha=1$, together with
  `Series.hasDerivAt_g`. The public `Bounds.pos_decreasing_convex`
  gives the first three signs used for monotonicity and convexity.
- **PROVED.** The scaling equations are
  `Bounds.ScalingWork.scaling_f` and `Bounds.ScalingWork.scaling_g_succ`,
  instantiated in `Bounds.fractional_system`. The endpoint ODEs are
  `Bounds.ode_one_base` and `Bounds.ode_one_succ`.
- **PROVED in prose.** Both constants are optimal. The series gives
  $f'(0)=-1/\phi(1)$, forcing any upper bound $C/(C+x)$ to have
  $C\ge\phi(1)$. Also $xf(x)\to\phi(0)$, forcing any lower bound
  $C/(C+x)$ to have $C\le\phi(0)$. For the fractional case, the upper
  bound gives $f(x)\to0$, and the chord inequality dominates the scaling
  integrand by $(1-\lambda)K$, an integrable function. Its pointwise
  limit is zero, so dominated convergence in the scaling equation proves
  the claimed limit. At $\alpha=1$, convexity gives
  $0\le-xf'(x)\le2(f(x/2)-f(x))\le2f(x/2)\to0$; the ODE then gives
  $xf(x)\to a=\phi(0)$.
- **PROVED in prose.** The argument applies to any coefficient sequence
  $c_n=\prod_{j=1}^n\phi(j)^{-1}$ with
  $\phi(s)=A+ds+\int_0^1(1-\lambda^s)K(\lambda)\,d\lambda$,
  $A>0$, $d\ge0$, $K\ge0$, $\int_0^1(1-\lambda)K<\infty$ and
  $\phi(n)\to\infty$. The ratio criterion again gives every derivative
  series. The same first-moment majorant gives the scaling hierarchy
  with the extra drift term $dxg_k'$. At a nonpositive minimum the
  left derivative is nonpositive, while the integral difference and
  forcing have the opposite sign, proving all signed derivatives positive.
  The lower bound follows from $f'\le0$. For the upper bound, the chord
  bounds the integral by $(\phi(1)-A-d)(1-f)$ and the tangent gives
  $-dxf'\le d(1-f)$; their sum gives
  $(\phi(1)+x)f\le\phi(1)$.
- **OPEN.** The boundary $l=m-1/\alpha$, the source's Conjecture 3.7,
  is not covered by this result.

## ASSUMED-UNVERIFIED

Exhaustive literature coverage, citation-index completeness and priority
are unverified. The bounded literature scope does not imply that no
other settlement exists.
