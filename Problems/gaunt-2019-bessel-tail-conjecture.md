---
slug: gaunt-2019-bessel-tail-conjecture
bibkey: gaunt2019besselintegrals
doi: 10.1090/proc/14433
triage: theorem
motivation_gids:
  - D5/S3/Analytic/GauntBesselTail/Result.result
url: https://arxiv.org/abs/1806.00524
---

# The sharp weighted Bessel K tail bound

## Problem

R. E. Gaunt, *Inequalities for some integrals involving modified Bessel
functions*, Proc. Amer. Math. Soc. 147 (2019), 2937–2951,
DOI 10.1090/proc/14433, arXiv:1806.00524v2, Conjecture 2.4,
manuscript page 7. Verbatim fragments from the supplied text extraction:

> Then, for all x > 0,

> We have equality in (2.17)

> in inequality (2.17) is best possible, in the sense that, for any

The extraction splits the displayed square roots and subscripts. The
complete mathematical statement, reconstructed outside the quotations,
uses $n<1$, $\nu\ge1-n+\sqrt{2(1-n)}$ and

$$p=\nu+n,\quad q=\sqrt{p^2-2\nu-1},\quad
\alpha_{\nu,n}=p-q,\quad\alpha'_{\nu,n}=p+q.$$

It asserts, for every $x>0$,

$$T(x):=\int_x^\infty t^{-\nu}K_p(t)\,dt>x^{-\nu}K_q(x).$$

For every $\beta\notin\{\alpha,\alpha'\}$, either
$x^{-\nu}K_{p-\beta}(x)<x^{-\nu}K_q(x)$ for every positive $x$,
or $T(y)<y^{-\nu}K_{p-\beta}(y)$ for some positive $y$.
At $n=1$ equality holds for every real $\nu$.

### Formal reading

Lean names have prefix `D5.S3.Analytic.GauntBesselTail.Result`.

| Object | Lean declaration | Correspondence |
| --- | --- | --- |
| Bessel K | `D5.S3.Analytic.GammaGammaNBU.Result.besselK` | The existing hyperbolic integral, DLMF 10.32.9, on positive arguments. |
| Two shifts | `alpha`, `alphaPrime` | Literal source square-root formulas. |
| Weighted upper tail | `tail` | Real-power weight on t>x>0. |
| Entire conjecture | `claim` | The conjunction of the strict bound, its either/or optimality, and the unrestricted real-order equality. |
| Settlement | `result` | Exactly `claim`. |

## Motivation

The source note is `D5/L/Asymptotics/gaunt2019besselintegrals`.
The reused integral representation is recorded in
`D5/L/Asymptotics/nist2026dlmfbesselkintegral`.
The question asks for the largest absolute order that can give a universal
lower expression with the fixed weight $x^{-\nu}$.

## Gap

The sharp order is fixed by $q^2=p^2-2\nu-1$. The required comparison is
not an ordinary monotonicity statement in the order: it also compares a
weighted tail with a point value. The strict lower bound, sharpness and
$n=1$ identity are separate clauses of `claim`.

## Route

The parameter range gives $q\ge0$, $q<\nu$ and $q+1<p$.
For $u>0$, the function $s\mapsto\cosh(u\sqrt{s})$ is strictly convex
on $[0,\infty)$. Its second derivative has the sign of
$v\cosh v-\sinh v$, which is positive for $v>0$.
Adjacent secants at $(q-1)^2,(q+1)^2,p^2$ give, when $q>0$,

$$\cosh(pu)>\cosh(qu)\cosh u+
\frac{\nu}{q}\sinh(qu)\sinh u.$$

At $q=0$, the tangent at $s=1$ gives
$\cosh(pu)>\cosh u+\nu u\sinh u$.
Put $S_r(u)=\sinh(ru)/r$ for $r\ne0$ and $S_0(u)=u$, and define

$$h_r(u)=\cosh(pu)-\cosh(ru)\cosh u-\nu S_r(u)\sinh u.$$

Integration by parts gives
$K_r(t)=t\int_0^\infty e^{-t\cosh u}S_r(u)\sinh u\,du$.
Differentiation under the integral and the fundamental theorem give

$$T(x)-x^{-\nu}K_r(x)=
\int_x^\infty t^{-\nu}\int_0^\infty e^{-t\cosh u}h_r(u)\,du\,dt.$$

A tilted Gaussian dominates each differentiated kernel. Weighted Bessel
functions vanish at infinity and are integrable on every positive tail.
The strict convexity comparison makes the right side positive at $r=q$.

For $r>q$, $h_r(0)=h_r'(0)=0$ and $h_r''(0)=q^2-r^2<0$.
Thus $h_r<0$ on a right-hand interval. A fixed inner subinterval gives
a negative contribution with a slower exponential decay rate than any
positive contribution outside that interval. Consequently the inner
integral, and then the tail difference, are negative for all sufficiently
large arguments. For $|r|<q$, strict order monotonicity gives $K_r<K_q$.
For $n=1$, the hyperbolic addition formula makes $h_\nu$ identically zero.

## Falsifier

A parameter choice in the stated range violating any clause of `claim`
would contradict the settlement. The critical proof boundaries are the
sign in the tail identity and the comparison of the two exponential
decay rates in the sharpness argument.

## Evidence

**PROVED.** `D5.S3.Analytic.GauntBesselTail.Result.result` proves the
complete conjunction. The statement retains all real parameters in the
source ranges, with no numerical truncation or additional assumptions.

The numerical material is in the pinned
[experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/772c30b3c223c572697b9fc0eee77e075fc400a1/experiments/gaunt-bessel-k-tail-conjecture).
Script: `gaunt-c24.py`; command: `python3 gaunt-c24.py`;
SHA-256: `7b236bb973966da6da54dd184d7a0452cd8288f50533b2037253778010075580`.
**COMPUTED.** Exit code 0 at 50 decimal digits. The grid has
$n\in\{0.5,0,-1,-3\}$, and for each n the three orders are
$\nu_{\min}$, $\nu_{\min}+0.3$, $\nu_{\min}+2$, where
$\nu_{\min}=1-n+\sqrt{2(1-n)}$. At
$x\in\{0.01,0.1,0.5,1,2,5,10,20\}$ the 96 strict-bound readings
have minimum relative gap approximately $2.324\times10^{-3}$.
For $r=q+1$, all 48 relative gaps at $x\in\{50,100,200,400\}$
are negative. At $n=1$, $\nu\in\{-0.7,0,0.5,3\}$ and
$x\in\{0.3,1,4\}$, the maximum absolute residual is approximately
$5.35\times10^{-51}$. These are finite-grid numerical results.

The supplied literature check found no settlement within the titles of
14 Semantic Scholar citing works and the relevant candidates examined.
Its searches used the title, arXiv identifier, Conjecture 2.4 and the
parameter-shift expression. This bounded scope does not establish
exhaustive coverage or priority. No new network search is asserted.

## Triage

### What the settlement shows

- **PROVED.** The decisive mechanism is strict convexity in the squared
  order, established by the private `squared_order_strictConvex`, together
  with `tail_identity`. The resulting strict lower bound is `strict_tail`.
- **PROVED.** Optimality is stronger than the source's existence clause:
  `larger_order_failure` proves failure at every sufficiently large x for
  each r>q. The full source either/or statement is part of `result`.
- **PROVED.** `n_one_identity` treats every real nu, including zero and
  negative orders; `result` includes this equality clause.
- **COMPUTED.** Numerical margins have the pinned script and tested scope
  in Evidence; they are finite-precision readings rather than uniform
  parameter estimates.
- **OPEN (formalization).** No statement about the analogous I_nu
  question is proved by this module. The mathematical question is settled
  in the literature: the supplied check identifies arXiv:2605.20983 as a
  resolution of Gaunt's Open Problem 2.10.
- **OPEN.** Whether the same squared-order convexity route settles the
  paper's other conjectures is not established. No additional source
  conjecture is inferred from this result.

## ASSUMED-UNVERIFIED

Exhaustive literature coverage, citation-index completeness and priority
are unverified. Google Scholar's complete cited-by list was not checked.
The I_nu literature statement is supplied bibliographic evidence, not a
fresh source verification. Numerical calculations use finite precision
and do not replace the parameter-uniform Lean proof.
