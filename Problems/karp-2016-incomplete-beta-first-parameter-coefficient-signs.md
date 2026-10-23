---
slug: karp-2016-incomplete-beta-first-parameter-coefficient-signs
bibkey: karp2016incompletebeta
doi: 10.1007/s10958-016-2958-z
triage: theorem
motivation_gids:
  - D5/S3/Analytic/IncompleteBetaShape/Result.result
url: https://arxiv.org/abs/1509.05120v1
---

# First-parameter coefficient signs of the normalized incomplete beta function

## Problem

Karp, *Normalized incomplete beta function: log-concavity in parameters
and other properties*, §3, Conjecture 2:

> Conjecture 2 The coefficients ψ_k are negative for all a, α, β > 0 and x ∈ (0, 1) if 0 < b < 1 and positive if b > 1, so that a → x^{−a}(1 − x)^{−b} I_x(a, b) is strictly coefficient-wise Wright log-convex on (0, ∞) for α, β > 0, x ∈ (0, 1) and 0 < b < 1; and a → x^{−a}(1 − x)^{−b} I_x(a, b) is strictly coefficient-wise Wright log-concave on (0, ∞) for α, β > 0, x ∈ (0, 1) and b > 1.

Equations (1) and (6) give

$$c_j(t,b)=\frac{\Gamma(t+b+j)}{\Gamma(b)\Gamma(t+j+1)},\qquad
\psi_n=\sum_{k=0}^n\bigl[c_k(a+\alpha,b)c_{n-k}(a+\beta,b)
-c_k(a,b)c_{n-k}(a+\alpha+\beta,b)\bigr],$$

$$\psi_{a,b,\alpha,\beta}(x)
=x^{2a+\alpha+\beta}(1-x)^{2b}\sum_{n\ge0}\psi_nx^n.$$

### Formal reading

Unless otherwise indicated, Lean names have prefix
`D5.S3.Analytic.IncompleteBetaShape`.

| Source object | Lean name | Correspondence |
| --- | --- | --- |
| $c_j(t,b)$ in (1) | `D5.S3.Analytic.IncompleteBeta.coeff` | The same Gamma quotient; no new coefficient definition. |
| $\psi_n$ in (6) | `Defs.psi` | Exactly the displayed finite convolution difference, with natural index $n$. |
| $S_n(p,q;b)$ | `Mixture.convolution` | $\sum_{k=0}^n c_k(p,b)c_{n-k}(q,b)$. |
| Uniform shifted beta mixture | `Mixture.mixtureDensity` | The average of Beta$(p+k+1,q+n-k+1)$ densities for $0\le k\le n$. |
| Sliding kernel | `Kernel.F`, `Kernel.H` | The uniform affine average and its beta average used below. |
| Conjecture 2 | `Defs.claim`, `Result.result` | Both strict signs for all real $a,b,\alpha,\beta>0$ and all natural $n$. |
| $x\in(0,1)$ | No additional coefficient hypothesis | The coefficients do not depend on $x$, so this quantifier is vacuous for them. |

## Motivation

The settling declaration is
`D5/S3/Analytic/IncompleteBetaShape/Result.result`.
The source note is `D5/L/Asymptotics/karp2016incompletebeta`.
Coefficient signs constrain each term of the normalized series separately,
strengthening the corresponding pointwise Wright inequalities.

## Gap

Status: **Proved** for all positive real $a,b,\alpha,\beta$ and every
natural $n$, including zero. Both $0<b<1$ and $b>1$ are included;
neither shift is restricted to integers.

## Route

For $p,q,b>0$, put $c=p+q$ and

$$K(c,n,b)=\frac{(n+1)\Gamma(c+n+2b)}{\Gamma(b)^2\Gamma(c+n+2)},
\qquad w_b(y)=[y(1-y)]^{b-1}.$$

Termwise beta integration gives

$$S_n(p,q;b)=K(c,n,b)\int_0^1 w_b(y)\rho_{p,q,n}(y)\,dy,$$

where $\rho_{p,q,n}$ is the uniform mixture of the beta densities
with shapes $p+k+1,q+n-k+1$. This mixture is the law of
$sv+(1-s)u$ for independent $v\sim\mathrm{Beta}(p,q)$,
$s\sim\mathrm{Beta}(c,n+2)$ and uniform $u$.
The map $(v,s)\mapsto(sv,s(1-v))$ has Jacobian $s$.
At fixed output $y$, its domain becomes $0<x<y$, $0<z<1-y$;
expanding $(1-x-z)^n=((y-x)+(1-y-z))^n$ and evaluating the
resulting beta integrals proves the affine identity.

Define

$$F_s(v)=\int_0^1w_b(sv+(1-s)u)\,du,\qquad
H_{c,n,b}(v)=\frac1{B(c,n+2)}\int_0^1s^{c-1}(1-s)^{n+1}F_s(v)\,ds.$$

The kernel $H$ is continuous and bounded on $[0,1]$ and symmetric
about $1/2$. For $0<s<1$ and $0<v<1$,

$$F_s'(v)=\frac{s}{1-s}\bigl(w_b(r)-w_b(\ell)\bigr),\qquad
\ell=sv,\quad r=sv+1-s,$$

$$r(1-r)-\ell(1-\ell)=s(1-s)(1-2v).$$

Consequently $H$ strictly increases on $(0,1/2]$ for $b>1$
and strictly decreases there for $0<b<1$. The bound
$|F_s(v)|\le B(b,b)/(1-s)$ gives an integrable majorant
for the $s$ average, including the singular regime $0<b<1$.

The affine identity yields

$$S_n(p,q;b)=K(c,n,b)\frac1{B(p,q)}
\int_0^1v^{p-1}(1-v)^{q-1}H_{c,n,b}(v)\,dv.$$

Apply the existing strict beta-mean comparison to $H$ for $b>1$
and to $-H$ for $0<b<1$. At fixed $p+q$, the convolution strictly
decreases with $|p-q|$ in the first case and strictly increases in
the second. The pairs $(a+\alpha,a+\beta)$ and
$(a,a+\alpha+\beta)$ have the same sum and half imbalances
$|\alpha-\beta|/2<(\alpha+\beta)/2$. Their comparison gives both signs.

## Falsifier

Positive real $a,b,\alpha,\beta$ and natural $n$ with
$\psi_n\ge0$ when $0<b<1$, or $\psi_n\le0$ when $b>1$,
would contradict the statement. Zero parameters and zero shifts
are outside its hypotheses; $b=1$ is outside both strict branches.

## Evidence

`D5/S3/Analytic/IncompleteBetaShape/Result.result` proves exactly
`Defs.claim`, with no additional hypotheses. Its principal dependencies
are `Result.convolution_strictAnti_imbalance` and
`Result.convolution_strictMono_imbalance`, which consume
`Mixture.convolution_eq_betaMean_H`,
`Mixture.convolution_eq_mixtureMean`, `Mixture.mixture_eq_affine`,
`Kernel.H_continuousOn`, `Kernel.H_bounded`, `Kernel.H_symm`,
`Kernel.H_strictMonoOn_of_one_lt` and
`Kernel.H_strictAntiOn_of_lt_one`.
The comparison is reused from
`D5.S3.Analytic.IncompleteBeta.Comparison.betaMean_strictAntiOn`.
Beta integration is reused from `D5.S3.Analytic.KummerRatio.BetaIntegral`
and `D5.S3.Analytic.KilbasSaigo.Bounds.FractionalCertificate`.
The geometric integral identity is reused from
`D5.S3.Quantum.Measurement.QubitIncompatibilityProbability.triangle_change_lintegral`,
restricted to a rectangle and with the two input coordinates exchanged.
The axiom closure of `Result.result` is
`{propext, Classical.choice, Quot.sound}`.

The proof route was derived with the assistance of the ChatGPT Pro model.
The source's Corollary 1 proves $0<b<1$ for all positive shifts and
$b>1$ for $\alpha\in\mathbb N$, $\beta\ge\alpha-1$;
it states the general case as Conjecture 2.
No settlement was found in the supplied bounded literature scope:
the source identifier and title with coefficient-wise log-concavity,
log-convexity and incomplete beta functions; the thirteen citing works
listed by OpenAlex, with the two concerning coefficient-wise
log-concavity read (arXiv:1906.04975 and arXiv:1611.06724);
and Kalmykov–Karp arXiv:1211.2882, Karp–Zhang arXiv:2305.09029
and Askitis arXiv:1710.09708.
This scope does not establish exhaustive citation-index coverage or priority.

## Triage

- **PROVED.** For every $a,\alpha,\beta>0$ and natural $n$,
  $\psi_n<0$ if $0<b<1$, and $\psi_n>0$ if $b>1$,
  by `Result.result`.
- **PROVED.** The beta-mixture representation and the affine mixture
  identity, by `Mixture.convolution_eq_mixtureMean` and
  `Mixture.mixture_eq_affine`.
- **PROVED.** For $c,b>0$, $H_{c,n,b}$ is bounded, continuous and
  symmetric on $[0,1]$; it strictly increases on $(0,1/2]$
  for $b>1$ and strictly decreases there for $0<b<1$, by `Kernel.H_bounded`,
  `Kernel.H_continuousOn`, `Kernel.H_symm`,
  `Kernel.H_strictMonoOn_of_one_lt` and `Kernel.H_strictAntiOn_of_lt_one`.
- **PROVED in prose.** For $b=1$, the Gamma quotient gives
  $c_j(t,1)=1$ for $t>0$, hence $\psi_n=0$.
  This boundary case is not asserted as an additional Lean theorem.
- **PROVED in prose.** At fixed $p+q$ with $p,q>0$, the uniform
  mixture of Beta$(p+k+1,q+n-k+1)$ has strictly smaller expectation
  of every continuous symmetric function strictly increasing toward
  $1/2$ as $|p-q|$ grows. Its affine average has the same strict
  midpoint order: the moving-window derivative compares the two
  endpoint values, whose distances from $1/2$ are strictly ordered
  before the midpoint. Beta averaging preserves strictness, and the
  existing beta-mean comparison applies. The affine identity is
  formalized; this general test-function conclusion is not an
  additional Lean theorem.
- **OPEN.** Nonuniform mixture weights are an open direction.

## ASSUMED-UNVERIFIED

Exhaustive literature coverage, citation-index completeness and priority
are unverified. Independent external-source confirmation of the supplied
bounded literature findings is unverified.
