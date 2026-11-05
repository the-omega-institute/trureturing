---
slug: karp-zhang-2023-conjecture-4-2
bibkey: karpzhang2023pochhammer
doi: 10.1007/s13540-023-00238-0
url: https://arxiv.org/abs/2305.09029
triage: theorem
motivation_gids:
  - D5/S3/Analytic/KarpZhangCatalanPower/Result.claim
  - D5/S3/Analytic/KarpZhangCatalanPower/Result.result
---

# Coefficientwise log-concavity and log-convexity of Catalan-power series

## Problem

Dmitrii Karp and Yi Zhang, *Log-concavity and log-convexity of series containing
multiple Pochhammer symbols*, arXiv:2305.09029v3, page 8, Conjecture 4.2:

> Assume that $\{h_k\}_{k=0}^{\infty}$ is log-concave (log-convex ) and independent of $\mu$. Then the function $\mu\to h(\mu;x)$ defined in (15) is coefficient-wise log-concave (log-convex ).

Formula (15) defines

$$
h(t;x)=\sum_{k\ge0}h_k a_k(t)x^k,\qquad
a_k(t)=\frac{(t)_{2k}}{(t+1)_k k!}.
$$

Definition 1.1, page 2, starts with a nonnegative nontrivial real sequence.
The log-concave class has $h_k^2\ge h_{k-1}h_{k+1}$ for every positive
integer $k$ and interval support, with the precise printed zero-support
disjunction. The log-convex clause reads:

> If $f_k^2\le f_{k-1}f_{k+1}$ for all $k\in\mathbb N$, the sequence is called log-convex (this inequality implies that a nontrivial sequence is strictly positive).

Here $\mathbb N=\{1,2,\ldots\}$. The literal inequalities permit the
exception supported on $\{0\}$; no extra strict-positivity assumption is
imposed. For $\mu,\alpha,\beta\ge0$, set

$$
\delta_m=\sum_{k=0}^{m}h_kh_{m-k}
\left[a_k(\mu+\alpha)a_{m-k}(\mu+\beta)
-a_k(\mu)a_{m-k}(\mu+\alpha+\beta)\right].
$$

The assertion is $\delta_m\ge0$ for log-concave $h$ and $\delta_m\le0$
for log-convex $h$, for every natural degree $m$ and every nonnegative
real base parameter and shifts. It concerns finite formal coefficients,
without convergence or growth assumptions.

All Lean names in the table have prefix `D5.S3.Analytic`.

| Source object | Lean name | Correspondence |
| --- | --- | --- |
| Formula (15) | `KarpZhangCatalanPower.Coeff.a` | Literal rising-factorial quotient, including $k!$. |
| Definition 1.1, log-concave class | `KarpZhangReciprocal.Result.IsLogConcave` | Existing predicate, including nontriviality and exact interval support. |
| Definition 1.1, log-convex class | `KarpZhangCatalanPower.Result.IsLogConvex` | Nonnegativity, nontriviality and adjacent inequalities at positive indices; no support restriction. |
| Turanian coefficient | `KarpZhangCatalanPower.Result.delta` | Exactly the finite Cauchy sum above. |
| Conjecture 4.2 | `KarpZhangCatalanPower.Result.claim` | Both implications for the same $h,\mu,\alpha,\beta,m$. |
| Settlement | `KarpZhangCatalanPower.Result.result` | A proof of exactly `claim`. |

## Motivation

The index law makes the unweighted transform log-neutral. The conjecture
asks whether weighting by either sequence class preserves the corresponding
coefficient sign for arbitrary real shifts. Positivity of the evaluated
series, integer-shift cases or finitely many degrees would not settle it.

## Gap

Status: **PROVED (Lean)** for both halves, including $\mu=0$. There is no
degree cutoff, no integrality restriction on the shifts, and no additional
positivity assumption on the log-convex sequence. Conjecture 3.8 is outside
this assertion.

## Route

Write $a_0(t)=1$ and, for $n\ge1$,

$$
a_n(t)=\frac{t}{n!}\prod_{r=n+1}^{2n-1}(t+r).
$$

These are the coefficients of the Catalan series power $C(x)^t$.
Their convolution index law and its derivative at zero give

$$
\sum_{k=0}^m a_k(s)a_{m-k}(t)=a_m(s+t),\qquad
 a_n'(t)=\sum_{j=1}^n b_j a_{n-j}(t),\qquad
 b_j=\frac{\binom{2j}{j}}{2j}>0.
$$

For $0<u<v$ and $i<l$, the adjacent-ratio comparison gives
$a_i(u)a_l(v)>a_l(u)a_i(v)$ (TP2). Put

$$
Z_{m,q}(u,v)=\sum_{k=q}^{m-q}a_k(u)a_{m-k}(v).
$$

Differentiating along $u+v=S$ and cancelling reflected overlapping
intervals leaves

$$
(\partial_u-\partial_v)Z_{m,q}
=\sum_{j=1}^m b_j\sum_{i\in R_{m,q,j}}
\left[a_i(u)a_{m-j-i}(v)-a_{m-j-i}(u)a_i(v)\right],
$$

where
$R_{m,q,j}=[\max(0,q-j),\min(q-1,m-q-j)]\cap\mathbb Z$.
Every surviving index satisfies $i<m-j-i$. Thus $Z$ increases towards
the balanced point on a line of constant parameter sum. Symmetry gives
nonnegative tails

$$
T_{m,q}=Z_{m,q}(\mu+\alpha,\mu+\beta)
-Z_{m,q}(\mu,\mu+\alpha+\beta)\ge0.
$$

The full tail $T_{m,0}$ is zero by the index law. At $\mu=0$ and $q\ge1$,
$a_k(0)=0$ at every index in the second product, so termwise nonnegativity
proves the same tail inequality.

With $H=\lfloor m/2\rfloor$ and $W_q=h_qh_{m-q}$, the existing generic
Abel identity gives

$$
\delta_m=W_0T_{m,0}+\sum_{q=1}^{H}(W_q-W_{q-1})T_{m,q}.
$$

The existing log-concave balancing theorem makes $W$ nondecreasing, including
all interval supports and zeros. In the log-convex class, $h_1=0$ implies
$h_n=0$ for every $n\ge1$, by induction in the adjacent inequalities.
Otherwise nonnegativity gives $h_1>0$; its adjacent inequality forces $h_0>0$
and induction forces every subsequent entry positive. Dividing adjacent
inequalities then shows that $h_{n+1}/h_n$ is nondecreasing. Therefore
$W_{q+1}\le W_q$ below the middle. The zero-tail case gives the same
inequality directly. Abel proves both signs and counts an even middle
index once. Empty increment sums cover $m=0,1$.

## Falsifier

A mismatch would include reversing the Turanian sign, dropping a factorial,
restricting shifts to integers, replacing interval support on the log-concave
side by adjacent inequalities alone, or assuming all log-convex entries
strictly positive. The derivative must be along constant parameter sum,
and reflected intervals with negative upper endpoints must be empty.
The settlement must prove the exact universal `claim` without placeholders
or additional axioms.

## Evidence

The source locator and quotations are in
`Library/Asymptotics/karpzhang2023pochhammer.md`; the printed pages are 2 and 8
of arXiv:2305.09029v3. The preregistration is
https://github.com/the-omega-institute/trureturing/issues/21083.
The coefficient, index, generator, reflected-interval and tail proofs share
`D5/S3/Analytic/KarpZhangCatalanPower/Result.lean`, which proves exactly
`claim`. The supporting declarations retain the `Coeff`, `Index` and
`Interval` namespaces within that module.
The sequence predicate, log-concave balancing and generic finite Abel identity
are reused from `D5/S3/Analytic/KarpZhangReciprocal/Result.lean`.

The paper argument is attributed by the coordinating research line to a
codex-cli research seat and an independent codex-cli referee seat. The Lean
implementation uses codex-cli, with Claude Opus 5.5 coordinating. This
attribution is separate from the mathematical evidence.

The scoped build of `D5.S3.Analytic.KarpZhangCatalanPower.Result` and
`D5.S3.Analytic.KarpZhangConjecture.Result` checks the settlement and the
consumer closure of the shared Abel declarations. The axiom closure of
every public theorem of the Catalan-power settling module
`D5.S3.Analytic.KarpZhangCatalanPower.Result` is contained in
$\{\texttt{propext},\texttt{Classical.choice},\texttt{Quot.sound}\}$.
Local compilation is distinct from freezing, publication and required CI.
No numerical computation is used as proof evidence.

## Triage

### What the settlement shows

- **PROVED (Lean):** The mechanism is index law ⇒ positive derivative
  generator $b_j=\binom{2j}{j}/(2j)$ ⇒ reflected-interval cancellation ⇒
  balancing increases interval convolutions ⇒ nonnegative tails ⇒ Abel gives
  both coefficient signs. The respective declarations are
  `Index.index_law`, `Index.b_eq_centralBinom`, `Index.b_pos`,
  `Interval.reflected_interval`, `Interval.slice_strictMonoOn`,
  `Interval.tail_nonneg` and `Result.result`, with prefix
  `D5.S3.Analytic.KarpZhangCatalanPower`.
- **PROVED (Lean, `Result.result`):** Both implications hold for every
  degree, nonnegative base parameter and nonnegative real shifts. This
  includes zero shifts, zero entries, finite and singleton log-concave
  supports, and the log-convex exception supported on $\{0\}$.
- **PROVED (in prose):** The sign argument generalizes to any formal family
  $A_t(x)=G(x)^t=\exp(tB(x))$, $G(0)=1$, with
  $B(x)=\log G(x)=\sum_{j\ge1}b_jx^j$ having $b_j\ge0$, whose coefficients
  satisfy $a_i(u)a_l(v)\ge a_l(u)a_i(v)$ for $0<u\le v$ and $i<l$.
  Indeed each $a_n(t)$ is a polynomial in $t$ with nonnegative coefficients,
  so is nonnegative for $t\ge0$. Formal differentiation gives
  $a_n'=\sum_{j=1}^n b_j a_{n-j}$. The reflected-interval identity above is
  purely finite reindexing, and every determinant on its right is
  nonnegative by TP2. Thus every constant-sum central convolution is
  nondecreasing up to its centre. Symmetry gives the tail inequality for
  positive base parameters, and polynomial continuity gives it at zero.
  The semigroup identity gives zero full tail; the same two balanced-weight
  inequalities and Abel give both signs. Strictness needs additional
  positivity and is not part of this generalization.
- **OPEN:** A general Lean theorem for that entire formal-family criterion;
  the present Lean theorem concerns the literal coefficients (15).
- **OPEN:** Joint log-concavity of arbitrary truncated interval convolutions
  is neither asserted nor needed. The proof uses only constant-sum balancing.
- **OPEN:** Conjecture 3.8 and any other assertion beyond the exact `claim`.
  The settlement removes the shift restrictions for Conjecture 4.2; it does
  not prove a one-sign-change property of the paper's paired kernel.

## ASSUMED-UNVERIFIED

Exhaustive literature coverage, citation-index completeness and priority
are unverified. The source and literature checks supplied in the
preregistration are coordinating-line evidence, not a new online search
by this offline implementation seat. The producer attribution is supplied
by that line. Four-slot escape registrations for the newly authored public
theorems of `D5.S3.Analytic.KarpZhangCatalanPower.Result` are not completed;
their proofs do not constitute those registrations. This audit boundary is associated with
preregistration #21083 and requires the corresponding owner registrations.
