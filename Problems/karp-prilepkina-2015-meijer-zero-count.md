---
slug: karp-prilepkina-2015-meijer-zero-count
bibkey: karpprilepkina2016gammaratio
doi: 10.1007/s40315-015-0128-9
triage: theorem
motivation_gids:
  - D5/S3/Analytic/MeijerZeroCount/Result.result
url: https://arxiv.org/abs/1501.05388
---

# The Karp–Prilepkina Meijer zero-count conjecture

## Problem

Karp and Prilepkina, *Completely monotonic gamma ratio and infinitely
divisible H-function of Fox*, arXiv:1501.05388v2, Section 2, Conjecture 1:

> If aᵢ ≥ 0, i = 1, …, p and Σᵢ₌₁ᵖ (bᵢ − aᵢ) > 0 then # zeros of G^{p,0}_{p,p}(x | b/a) on (0, 1) ≤ # zeros of v(t) on (0, 1).

Here $p\ge1$, $a_i,b_i$ are real,

$$v(t)=\sum_{k=1}^p(t^{a_k}-t^{b_k}),\qquad
\psi=\sum_{i=1}^p(b_i-a_i),$$

and the contour-integral definition is

$$G^{p,0}_{p,p}\!\left(x\;\middle|\;\begin{matrix}b\\a\end{matrix}\right)
=\frac{1}{2\pi i}\int_L
\frac{\prod_{i=1}^p\Gamma(a_i+s)}
{\prod_{i=1}^p\Gamma(b_i+s)}x^{-s}\,ds.$$

The contour separates the numerator poles in the usual Mellin–Barnes
representation. The zero counts below count distinct zeros.

### Formal reading

All Lean names below have prefix `D5.S3.Analytic.MeijerZeroCount`.

| Source object | Lean name | Correspondence |
| --- | --- | --- |
| $R(s)=\prod_i\Gamma(a_i+s)/\prod_i\Gamma(b_i+s)$ | `Defs.gammaQuot` | Complex Gamma quotient of the real parameter vectors. |
| $G^{p,0}_{p,p}(x\mid b/a)$ | `Defs.meijerG` | `mellinInv 1 (gammaQuot a b) x`, with normalization $1/(2\pi)$ in the real integral. |
| $v(t)=\sum_k(t^{a_k}-t^{b_k})$ | `Defs.control` | Real powers of real arguments; the comparison uses $0<t<1$. |
| $p\ge1$, $a_i\ge0$, $\psi>0$ | `Defs.claim` | The formal claim restricts to $\psi>1$. It quantifies over natural $p$; the case $p=0$ cannot satisfy $\psi>1$. |
| Number of zeros on $(0,1)$ | `Set.encard` of each displayed zero set | Extended natural cardinality, including infinite zero sets. |
| $a=(n+c,n+c)$, $b=(c,2n+d+c)$ | `Result.family` | All natural $n,d\ge2$ and real $c>0$; $p=2$ and $\psi=d$. |
| Refutation of the comparison | `Result.result` | The unconditional theorem has type `¬ Defs.claim`. |

The formal claim restricts to $\psi>1$, where the contour may be taken
as the vertical line $\Re s=1$. Since $a_i\ge0$, this line is to the
right of every numerator Gamma pole. The Gamma quotient decays as
$O(|\Im s|^{-\psi})$ on this line, so the integral is absolutely
convergent. A counterexample in this restricted range is also a
counterexample to the source statement with $\psi>0$.

## Motivation

The settling declaration is `D5/S3/Analytic/MeijerZeroCount/Result.result`.
The source note is `D5/L/Asymptotics/karpprilepkina2016gammaratio`.
The conjecture compares oscillation of an inverse Mellin transform
with a finite power sum built from the same parameter vectors.

## Gap

Status: **Refuted**. The family $a=(n+c,n+c)$,
$b=(c,2n+d+c)$ with $n,d\ge2$ and $c>0$ has $n$ interior zeros of
$G$ and exactly one of $v$. The excess $n-1$ is unbounded even for
fixed $p=2$ and $\psi=d=2$.

## Route

Put $N=n+d-1$. Gamma recurrence gives

$$R(s)=\frac{(s+c)_n}{(s+c+n)_{n+d}}
=\sum_{k=0}^{N}\frac{A_k}{s+c+n+k},\qquad
A_k=\frac{(-1)^{n+k}(n+k)!}{(k!)^2(N-k)!}.$$

The partial fractions follow by polynomial interpolation at the
distinct denominator roots. Define $W(x)=x^n(1-x)^N$ and, on $(0,1)$,

$$f(x)=\frac{(-1)^n}{N!}x^{n+c}W^{(n)}(x)
=\sum_{k=0}^{N}A_k x^{n+c+k},$$

extending $f$ by zero outside that interval. Its Mellin transform is
$R(s)$ for $\Re s>0$. On the inversion line,
$|R(1+it)|\le(1+t^2)^{-1}$; continuity in the interior and Mellin
inversion give $G=f$ there.

Repeated Rolle arguments use the endpoint factors of $W$ to produce
at least $n$ distinct interior zeros of $W^{(n)}$. Dividing out
$(1-x)^{d-1}$ leaves a polynomial of degree at most $n$, proving the
matching upper bound. The nonvanishing factor $x^{n+c}(-1)^n/N!$
preserves this zero set.

For the control function,

$$v(x)=x^c(2x^n-1-x^{2n+d}).$$

The second factor is
$(x-1)h(x)$, where
$h(x)=\sum_{j=0}^{n-1}x^j-x^n\sum_{j=0}^{n+d-1}x^j$.
It is positive at zero and negative at one. Its normalization
$h(x)/x^n=\sum_{j=0}^{n-1}x^{j-n}
-\sum_{j=0}^{n+d-1}x^j$ is strictly decreasing on $(0,1)$,
which proves existence and uniqueness of its interior zero.

## Falsifier

The explicit admissible vectors $a=(3,3)$ and $b=(1,7)$ have
$\psi=2$. Their interior zero counts are two for $G$ and one for
$v$, contradicting the proposed inequality $2\le1$.

## Evidence

`D5/S3/Analytic/MeijerZeroCount/Result.result` proves exactly
`¬ Defs.claim`, with no additional hypotheses. Its principal
dependency is `Result.family`; both zero-count conjuncts are used
in the contradiction. The analytic dependencies are
`Mellin.gammaQuot_family`, `Mellin.mellin_f` and
`Mellin.meijerG_eq_f`. The polynomial expansion and count are
`Rodrigues.f_eq_sum` and `Rodrigues.zeros_f`; the control count is
`Control.zeros_control`. The axiom closure of `Result.result` is
`{propext, Classical.choice, Quot.sound}`.

The refutation route was derived with the assistance of the ChatGPT Pro model.
The source proves that an interior zero of $G$ forces a zero of $v$.
Karp–Prilepkina 2017, on delta-neutral H-functions, settles the
different Conjecture 2. No settlement of Conjecture 1 was found in
the searched scope: the source and its identifier, the authors' work
on Gamma quotients and zero counts, the 2017 delta-neutral paper,
Berg–Çetinkaya–Karp 2021, Karp's publication list and the distinct
Toeplitz-determinant conjecture discussed in arXiv:2610.18895.
This bounded scope does not establish exhaustive literature
coverage or priority.

## Triage

- **PROVED.** For all integers $n,d\ge2$ and real $c>0$, with
  $a=(n+c,n+c)$ and $b=(c,2n+d+c)$, $G^{2,0}_{2,2}$ has exactly
  $n$ distinct zeros on $(0,1)$ and $v$ exactly one
  (`Result.family`). Conjecture 1 fails (`Result.result`), and
  the excess $n-1$ is unbounded for fixed $p=2$, $\psi=2$.
- **PROVED.** On $(0,1)$,
  $G(x)=x^{n+c}(-1)^nW^{(n)}(x)/N!$, with
  $W(x)=x^n(1-x)^{n+d-1}$ and $N=n+d-1$
  (`Mellin.meijerG_eq_f`, `Rodrigues.f`, `Rodrigues.rodriguesPoly`).
- **PROVED in prose.** The interior zeros are simple. After removing
  $(1-x)^{d-1}$ from $W^{(n)}$, the remaining polynomial has degree
  at most $n$ and $n$ distinct roots, hence degree $n$ and no repeated
  root. The other factors are nonzero on $(0,1)$. The shifted Jacobi
  Rodrigues identity gives
  $G(x)=[n!/(n+d-1)!]x^{n+c}(1-x)^{d-1}
  P_n^{(d-1,0)}(2x-1)$.
  The same family refutes the unit-scale case of the source's
  Conjecture 3, because its Fox H-function specializes to this
  Meijer G-function when every scale is one. Simplicity, the Jacobi
  identity and this specialization are prose consequences, not
  separate Lean theorems.
- **COMPUTED.** For $n=d=2$, $c=1$,
  $G(x)=x^3(1-x)(10x^2-8x+1)/3$ on $(0,1)$, with zeros
  $(4\pm\sqrt6)/10$. Also $v(x)=x(2x^2-1-x^6)$ has its single
  interior zero at $\sqrt{(\sqrt5-1)/2}$.
- **OPEN.** Conjecture 1 on the remaining parameter range
  $0<\psi\le1$, a zero-count bound depending on further structure,
  and the Fox H Conjecture 3 in general remain outside this result.

## ASSUMED-UNVERIFIED

Exhaustive literature coverage, citation-index completeness and priority
are unverified. The bounded literature scope does not imply that no
other settlement exists.
