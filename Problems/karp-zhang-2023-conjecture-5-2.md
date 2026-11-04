---
slug: karp-zhang-2023-conjecture-5-2
bibkey: karpzhang2023pochhammer
doi: 10.1007/s13540-023-00238-0
url: https://arxiv.org/abs/2305.09029
triage: theorem
motivation_gids:
  - D5/S3/Analytic/KarpZhangConjecture/Result.claim
  - D5/S3/Analytic/KarpZhangConjecture/Result.result
---

# Coefficientwise log-concavity of the two Karp--Zhang series

## Problem

Dmitrii Karp and Yi Zhang, *Log-concavity and log-convexity of series containing
multiple Pochhammer symbols*, arXiv:2305.09029v3, page 12, Conjecture 5.2:

> Suppose that $\{y_k\}_{k=0}^{\infty}$ is a log-concave sequence. Then the functions $\mu\to\widetilde y(\mu;x)$ and $\mu\to\widehat y(\mu;x)$ are coefficient-wise log-concave on $\mu>0$.

The two series are

$$
\widetilde y(\mu;x)=\sum_{k=0}^{\infty}y_k\frac{(2\mu)_k}{(\mu)_k k!}x^k,
\qquad
\widehat y(\mu;x)=\sum_{k=0}^{\infty}y_k\frac{\Gamma(\mu+k)}{\Gamma(2\mu+k)k!}x^k.
$$

Here $(a)_k$ is the rising factorial. Definition 1.1, page 2:

> Let $\{f_k\}_{k=0}^{\infty}$ be a non-negative nontrivial real sequence. We call $\{f_k\}_{k=0}^{\infty}$ log-concave (or Pólya frequency two – $PF_2$, or doubly positive) if $f_k^2\ge f_{k-1}f_{k+1}$ for each $k\in\mathbb N$, and $\{f_k\}_{k=0}^{\infty}$ is supported on an interval of integers (i.e., $f_N=0$ implies either $f_{N+i}=0$ for all $i\in\mathbb N_0$ or $f_{N-i}=0$ for $i=0,\ldots,N$).

The Lean predicate retains nonnegativity, nontriviality, adjacent inequalities
for positive natural indices, and the printed zero-support disjunction.
Natural subtraction is used only with the stated bounds.

For either series $f$, coefficientwise log-concavity means that every
coefficient of

$$
f(\mu+\alpha;x)f(\mu+\beta;x)-f(\mu;x)f(\mu+\alpha+\beta;x)
$$

is nonnegative for every $\mu>0$ and every real $\alpha,\beta\ge0$.
This is an assertion about finite Cauchy sums in each natural degree, so it
requires no convergence or growth assumption on $y$.

Formal correspondence. All Lean names below have prefix `D5.S3.Analytic`.

| Source object | Lean name | Correspondence |
| --- | --- | --- |
| Definition 1.1 | `KarpZhangReciprocal.Result.IsLogConcave` | All four sequence conditions, including nontriviality and the exact zero convention. |
| Reciprocal-series coefficient before multiplication by $y_k$ | `KarpZhangReciprocal.Coeff.c` | $(2\mu)_k/((\mu)_k k!)$. |
| Reciprocal Turanian coefficient | `KarpZhangReciprocal.Result.delta` | The degree-$m$ finite Cauchy coefficient with both factorials retained. |
| Gamma-series coefficient before multiplication by $y_k$ | `KarpZhangGamma.Series.gammaCoeff` | $\Gamma(\mu+k)/(\Gamma(2\mu+k)k!)$. |
| Gamma Turanian coefficient | `KarpZhangGamma.Series.gammaDelta` | The degree-$m$ finite Cauchy coefficient of the gamma-series Turanian. |
| Conjecture 5.2 | `KarpZhangConjecture.Result.claim` | Both coefficient inequalities for the same $y,\mu,\alpha,\beta,m$, universally quantified. |
| Settlement | `KarpZhangConjecture.Result.result` | A proof of exactly `claim`. |

## Motivation

The conjecture asks for preservation of coefficientwise log-concavity by two
different parameter-dependent transforms of an arbitrary log-concave
sequence. Nonnegativity of a series at positive arguments would not suffice:
the assertion must hold separately in every coefficient and for arbitrary
nonnegative real shifts.

## Gap

Status: **Proved (Lean)** for both halves of Conjecture 5.2. The result has
neither a degree cutoff nor an integrality restriction on either shift.
Conjectures 3.8 and 4.2 of the same paper remain open in this development.

## Route

For the reciprocal series, put $c_k(t)=(2t)_k/((t)_k k!)$ and

$$
F_{m,L,U}(s,t)=\sum_{k=L}^{U}c_k(s)c_{m-k}(t).
$$

On a line $s+t=S$, normalize the summands to a probability vector $\pi$.
The second derivative of the logarithm of their sum is the score variance
minus the expected negative logarithmic curvature. Reversible birth-and-death
rates on the finite index interval, with rates zero at its endpoints, give a
curvature-weighted variance inequality. The coefficient curvature estimate
absorbs its edge terms, proving concavity of $\log F_{m,L,U}(s,S-s)$.
Only this direction of concavity is needed. For a symmetric interval,
symmetry under $s\leftrightarrow t$ then gives

$$
F_{m,q,m-q}(\mu,\mu+\alpha+\beta)
\le F_{m,q,m-q}(\mu+\alpha,\mu+\beta).
$$

Log-concavity and interval support of $y$ imply that
$W_q=y_qy_{m-q}$ increases towards the central index. Finite Abel summation
expresses the reciprocal Turanian coefficient as $W_0$ times the full tail
plus the increments $W_{q+1}-W_q$ times the successive symmetric tails.
Every factor is nonnegative. This is
`KarpZhangReciprocal.Result.reciprocal_half`.

For the gamma series, introduce the formal exponential smoothings

$$
P_p(z)=\sum_{r\ge0}y_{p+r}\frac{z^r}{r!},
\qquad
H(a;z,w)=\sum_{j\ge0}\frac{P_{2j}(z)}{j!\Gamma(a+j)}w^j.
$$

Simultaneous induction in coefficient degree, using Pascal's recurrence,
shows that $P_{p+1}P_{q+1}-P_pP_{q+2}$ has nonnegative coefficients when
$p\le q+1$. Consequently the coefficient weights in
$P_{2k}P_{2(m-k)}$ increase towards the centre. Pair the reciprocal-gamma
kernel at $k$ and $m-k$, counting the middle term once. A finite Vandermonde
identity and log-convexity of Gamma show that the kernel's total is
nonnegative. The Gamma recurrence propagates nonpositivity of the four-term
bracket backwards, establishing at most one change from negative to positive.
The finite weighting principle therefore proves nonnegativity of every
bivariate Turanian coefficient of $H$.

Finally Gamma duplication and a simultaneous recurrence in degree give

$$
\frac{\Gamma(t+n)}{\Gamma(2t+n)n!}
=\sqrt\pi\,2^{1-2t}
\sum_{j=0}^{\lfloor n/2\rfloor}
\frac{1}{(n-2j)!j!\Gamma(t+1/2+j)2^{n-2j}16^j}.
$$

Thus the gamma series is $\sqrt\pi\,2^{1-2t}H(t+1/2;x/2,x^2/16)$.
The scale products at $t+\alpha,t+\beta$ and $t,t+\alpha+\beta$ agree and
are positive. Each substituted coefficient is a finite nonnegative weighted
sum of the bivariate coefficients. This proves
`KarpZhangGamma.Series.gamma_half`. The settling `result` combines the two
halves without changing any hypothesis.

## Falsifier

The correspondence would fail if either coefficient omitted a factorial,
reversed the Turanian sign, restricted a shift to integers, or replaced the
source's interval-support condition by adjacent inequalities alone.
The paired kernel must count its middle index once. The positive diagonal
substitution must retain every index satisfying $r+2j=n$. The exact universal
claim and both imported halves must compile without proof placeholders or
additional axioms.

## Evidence

The source is arXiv:2305.09029v3, pages 2 and 12, with DOI
10.1007/s13540-023-00238-0; the quotation and sequence convention are recorded
in `Library/Asymptotics/karpzhang2023pochhammer.md`. The reciprocal proof is in
`D5/S3/Analytic/KarpZhangReciprocal/{BirthDeath,IntervalConvolution,Result}.lean`;
the gamma proof is in
`D5/S3/Analytic/KarpZhangGamma/{Weighting,Smoothing,Result,Series}.lean`.
`D5/S3/Analytic/KarpZhangConjecture/Result.lean` states `claim` and proves it as
`result` by the two imported half theorems.

The paper proofs were written with the assistance of codex-cli research seats and checked by independent codex-cli referee seats, the Lean proofs were drafted with the assistance of codex-cli seats, and the work was orchestrated with the assistance of Claude Opus 5.5.

The settlement is associated with preregistration
https://github.com/the-omega-institute/trureturing/issues/20997.
The scoped Lean build of `D5.S3.Analytic.KarpZhangConjecture.Result` verifies
the settling theorem and its import closure. Its axiom closure is contained
in $\{\texttt{propext},\texttt{Classical.choice},\texttt{Quot.sound}\}$.
This local verification is distinct from publication, freezing and required CI.

## Triage

### What the settlement shows

The reciprocal mechanism is variance absorption for interval convolutions,
followed by symmetric-tail balancing and Abel summation. The gamma mechanism
is preservation of balanced minors under exponential smoothing, a single
negative-to-positive sign change in the reciprocal-gamma kernel, and a
positive diagonal transformation. Both mechanisms are uniform in coefficient
degree and allow arbitrary nonnegative real shifts, including zero. The
conclusions concern formal coefficients; analytic evaluation additionally
requires the relevant convergence hypotheses. Conjecture 5.2 can therefore
be used as a proved coefficient inequality under precisely its printed
sequence conditions. This supplies neither a new hypothesis nor a proof of
the paper's other conjectures.

- **PROVED (Lean, `KarpZhangReciprocal.Result.reciprocal_half`):** Every
  reciprocal-series Turanian coefficient is nonnegative for every admissible
  sequence, positive base parameter and nonnegative real shifts.
- **PROVED (Lean, `KarpZhangGamma.Series.gamma_half`):** Every gamma-series
  Turanian coefficient is nonnegative under the same conditions.
- **PROVED (Lean, `KarpZhangConjecture.Result.result`):** The conjunction of
  both universal coefficient assertions, exactly `claim`.
- **OPEN:** Conjectures 3.8 and 4.2 of the same paper. Numerical support is
  reported by the research line; neither conjecture is proved here. The
  numerical scope has not been independently revalidated in this delivery.

## ASSUMED-UNVERIFIED

Exhaustive literature coverage, citation-index completeness and priority are
unverified. Numerical support for Conjectures 3.8 and 4.2 is supplied by the
research line; no numerical experiment or uniform extension is certified by
this delivery. The producer attribution above is supplied by the coordinating
research line. Four-slot escape registrations for the public theorems of the
seven supporting modules and for the settling `result` are not completed in
this delivery; their mathematical proofs do not constitute those registrations.
