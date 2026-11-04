---
slug: karp-zhang-2023-conjecture-3-8
bibkey: karpzhang2023pochhammer
doi: 10.1007/s13540-023-00238-0
url: https://arxiv.org/abs/2305.09029
triage: theorem
motivation_gids:
  - D5/S3/Analytic/KarpZhangNinh/Result.claim
  - D5/S3/Analytic/KarpZhangNinh/Result.result
---

# Coefficientwise log-concavity of the triple rising-factorial series

## Problem

Dmitrii Karp and Yi Zhang, *Log-concavity and log-convexity of series containing
multiple Pochhammer symbols*, arXiv:2305.09029v3, page 8, Conjecture 3.8:

> Assume that $\{f_n\}_{n=0}^{\infty}$ is log-concave and independent of $\mu$. Then the function
>
> $$
> \mu\to f(\mu;x)=\sum_{n=1}^{\infty} f_n\frac{(\mu)_{3n}}{(3n-1)!}x^n
> $$
>
> is coefficient-wise log-concave.

Definition 1.1, page 2, uses nonnegative, nontrivial real sequences,
$f_k^2\ge f_{k-1}f_{k+1}$ for positive natural $k$, and interval support.
In particular, internal zeros are excluded, but zero endpoints and finite
supports are allowed. Define

$$
a_0(t)=0,\qquad a_n(t)=\frac{(t)_{3n}}{(3n-1)!}\quad(n\ge1),
$$

and, for every natural $m$ and nonnegative real $\mu,\alpha,\beta$,

$$
\delta_m=\sum_{k=0}^{m} f_kf_{m-k}
\left[a_k(\mu+\alpha)a_{m-k}(\mu+\beta)
-a_k(\mu)a_{m-k}(\mu+\alpha+\beta)\right].
$$

The assertion is $\delta_m\ge0$ for every such sequence, parameter triple
and degree. The endpoint summands vanish. These are finite formal Cauchy
coefficients, without convergence or growth assumptions.

The coefficient-wise convention on printed page 1 reads:

> if the coefficients $\delta_k$ at all powers of $x$ in (2) are non-negative (non-positive) for all $\alpha,\beta\ge0$ we will say that $\mu\to f(\mu;x)$ is coefficient-wise log-concave (log-convex ).

The Lean namespace prefix is `D5.S3.Analytic`. The coefficient is
`KarpZhangNinh.Result.Kernel.a`, the finite Turanian is `KarpZhangNinh.Result.delta`,
the sequence predicate is the reused
`KarpZhangReciprocal.Result.IsLogConcave`, and the universal proposition is
`KarpZhangNinh.Result.claim`.

## Motivation

The conjecture is the remaining multiplier-three case of the source's
rising-factorial family. Positivity of evaluated series, integer shifts,
or a bounded set of degrees does not imply its coefficient assertion.
The sequence must be fixed independently of the parameters.

## Gap

The required conclusion is the exact universal `Result.claim`.
`Result.result` proves it through a nonnegative full convolution sum,
one-sign-change central tails and the existing finite Abel decomposition.
The homogeneous and beta-lifting inequalities are uniform in the degree.

## Route

Put $N=3m$ and

$$
P_N(x,y)=\sum_{\substack{0\le k\le N\\3\mid k}}
 k(N-k)\binom Nk x^ky^{N-k}.
$$

The binomial residue counts obey Pascal recurrence and a six-periodic
closed form. For the finite differences $A_n$ and $T_n(N)$ this gives

$$
3A_n=2^{n-1}+\alpha_n,\qquad
3T_n(N)=(N-n)2^{n-1}+(N-1)\alpha_n-(n-1)\beta_n,
$$

where the formulas for $\alpha_n,\beta_n$ are selected by $n$ modulo six. Elementary uniform
exponential bounds make both quantities nonnegative for $1\le n<N$
and $3\mid N$. For $d>0$, the shear $y=x+d$ gives

$$
\frac{(\partial_x-\partial_y)P_N(x,y)}{y-x}\bigg|_{y=x+d}
=\sum_{n=1}^{N-1}n\binom Nn T_n(N)x^{n-1}d^{N-n-1}.
$$

A positive term makes $t\mapsto P_N(t,1-t)$ strictly increasing on
$(0,1/2]$ when $m\ge2$.

For a symmetric homogeneous polynomial
$P(x,y)=\sum_{k=0}^N c_kx^ky^{N-k}$, beta moments identify

$$
\frac{\sum_{k=0}^N c_k(u)_k(v)_{N-k}}{(u+v)_N}
=\frac{1}{B(u,v)}\int_0^1 P(t,1-t)t^{u-1}(1-t)^{v-1}\,dt
\quad(u,v>0).
$$

The reused symmetric beta comparison, extended from strictly increasing
to nondecreasing integrands by a positive quadratic perturbation and a
limit, transfers balancing monotonicity to the rising-factorial lift.
No coefficient-sign assumption is needed for this preservation theorem.
Factorial normalization identifies the lift of $P_{3m}$ with
$(3m)!\sum_{k=0}^m a_k(u)a_{m-k}(v)$, giving the nonnegative full tail.

Lemma 3.1, printed page 4, states:

> Let $k,m\in\mathbb N_0$ with $k\le m/2$, $\mu\ge0$ and $\alpha,\beta>0$. Set
>
> $$
> T_{k,m}:=(\mu+\alpha)_k(\mu+\beta)_{m-k}+(\mu+\alpha)_{m-k}(\mu+\beta)_k
> -(\mu)_k(\mu+\alpha+\beta)_{m-k}-(\mu)_{m-k}(\mu+\alpha+\beta)_k.
> $$
>
> If $T_{k,m}\le0$ for some $1\le k\le m/2$, then $T_{k-1,m}<0$.

Formula (8) is `KarpZhangNinh.Result.Kernel.pairPoch`, with $a,b,c,N$
for $\mu,\alpha,\beta,m$. The theorem
`KarpZhangNinh.Result.Kernel.paired_sign_step` uses the positive-$\mu$
specialization of the source's $\mu\ge0$ implication.

For positive parameters the paired Pochhammer kernel has at most one
negative-to-positive sign change. Backward length recurrence proves this
before factorial division; applying it three times gives the needed
multiplier-three assertion. The existing finite one-sign-change weighting
principle gives every central tail. The existing Abel decomposition then
expresses $\delta_m$ as a sum of these tails times nonnegative increments
of $f_kf_{m-k}$. Polynomial continuity supplies all zero-parameter cases.

## Falsifier

A failure includes reversing the Turanian, dropping either factorial,
allowing internal zeros without proof, weakening arbitrary real shifts to
integers, imposing a degree cutoff, or counting an even middle index twice.
The beta comparison must use the same constant parameter sum throughout.
The settlement must prove the exact `claim` without additional axioms,
placeholders, or an assumed full-tail inequality.

## Evidence

The source quotation and locator are in
`Library/Asymptotics/karpzhang2023pochhammer.md`; the preregistration is
https://github.com/the-omega-institute/trureturing/issues/21124.
The candidate, source and literature work was produced by the Claude Opus 5.5
orchestrator. The paper proof was written with the assistance of two serial
codex-cli research seats (`gpt-6.1-sol, high`) and checked by an independent
codex-cli review seat; the Lean proofs were drafted with the assistance of
codex-cli seats. The research and checking seats belong to a single model
family, so their agreement is not a claim of model diversity. The paper proof
gives the all-degree homogeneous positivity, the beta-lifting theorem and
the paired-sign/Abel reduction.

The Lean sources are
`D5/S3/Analytic/KarpZhangNinh/Beta.lean` (including the `Homogeneous` namespace)
and
`D5/S3/Analytic/KarpZhangNinh/Result.lean`.
`Result.result : Result.claim` is kernel-checked by the scoped settling-module
build. This is distinct from freezing and Scribe resolution admission.
The generic beta comparison and gamma–Pochhammer moment machinery are
reused from their existing D5 owners. The sequence predicate, balanced
products, finite pairing and Abel identity are reused from the existing
Karp–Zhang developments.

## Triage

### What the settlement shows

- **PROVED:** The decisive mechanism is homogeneous
  trisection positivity, followed by symmetric beta lifting, paired-sign
  propagation and finite Abel weighting. The exact universal target is
  `KarpZhangNinh.Result.result : KarpZhangNinh.Result.claim`.
- **PROVED:** The reusable tool is the general theorem
  `KarpZhangNinh.Beta.lift_monotoneOn`: a symmetric homogeneous polynomial
  whose unit-sum slice is nondecreasing towards its centre has a
  rising-factorial lift with the same balancing property. The coefficients
  may have either sign; closed endpoints and total parameter zero are included.
- **OPEN:** Independent verification of the source-reported numerical boundary
  is not supplied. The source report on page 4 states: “In this section we will prove
  this conjecture for r = 2 and disprove numerically for r = 4 (strongly
  suggesting that is it also wrong for r > 4). The case r = 3 remains open
  and is formulated in the form of Conjecture 3.8.” Remark 3.7, page 8,
  reports that the analogous unweighted family is neither coefficient-wise
  log-convex nor coefficient-wise log-concave for $r\ge4$ by numerical
  computations. These are attributed source computations, not a formal
  all-parameter refutation or a new local experiment. No reproducible
  experiment entry is claimed for the authors' computation.
- **OPEN:** The homogeneous positivity argument uses trisection. No formal
  multiplier-four refutation or theorem for every multiplier greater than
  four is included; the numerical failure boundary retains its source attribution.
- **OPEN:** All-degree coefficient positivity of the full sheared
  rising-factorial derivative quotient and joint log-concavity of arbitrary
  interval convolutions are outside the settled claim.
- **PROVED:** `KarpZhangNinh.Result.result` gives the exact multiplier-three
  conclusion and resolves the source's remaining case; the source's multiplier-two result
  and reported multiplier-four failure keep their respective scopes.

## ASSUMED-UNVERIFIED

Exhaustive literature coverage, citation-index completeness and priority
are unverified. The preregistration supplies the prior literature checks
and attribution of the research proof. No new online search is included.
Kernel compilation does not establish freezing, publication or required CI.
The new public theorems have no completed four-slot escape registrations;
the missing owner registrations are associated with preregistration #21124.
The scoped Scribe emission includes the Proved resolution node. This does
not establish freezing; this implementation does not write frozen state.
