---
slug: zelinsky-zhang-2025-conjecture-15
bibkey: zelinskyzhang2025klprimitive
doi: 10.48550/arXiv.2501.04209
url: https://arxiv.org/abs/2501.04209v2
triage: theorem
motivation_gids:
  - D5/S3/Arith/Abundancy/ZelinskyZhangKLPrimitive.result
---

# Zelinsky–Zhang's deficient KL-primitive integers

## Problem

Zelinsky and Zhang, arXiv:2501.04209v2, page 12, Conjecture 15:

> There are infinitely many n which are deficient and KL-primitive.

Equation (6) defines

$$
KL(n)=\sum_{d\mid n}d\log\frac{d}{2\varphi(d)}.
$$

Definition 1 on page 12 calls n KL-primitive when KL(n)≥0 and
KL(d)<0 for every proper positive divisor d of n. Deficiency means
σ(n)<2n, with σ the sum of positive divisors. All integers in the
conjecture are positive. The equivalent bounded-existence target is:
for every natural B there is n>B with n>0, σ(n)<2n, and n KL-primitive.

## Motivation

KL-primitivity and primitive non-deficiency impose minimality for
different divisor inequalities. Deficient KL-primitive integers separate
these two thresholds. Conjecture 15 is the named external problem in
preregistration #31617; the source is a public preprint.

## Gap

The paper's proposed family 2^{k−1}p depends on primes of the forms
2^k+1 or 2^k+3. The required infinitude does not follow from the displayed
finite examples or the positivity of KL at each admissible example.
A construction must cross the KL threshold while remaining strictly
below the abundancy threshold, and must retain unboundedness when a
KL-primitive divisor is extracted.

## Route

For a prime p put

$$
f(p)=\frac{p}{p+1}\log\frac p{p-1},\qquad
g(p)=\log(1+1/p),\qquad \delta(p)=f(p)-g(p).
$$

If p does not divide n, the coprime divisor decomposition gives

$$
\begin{aligned}
KL(pn)&=(p+1)KL(n)+p\sigma(n)\log\frac p{p-1},\\
\sigma(pn)&=(p+1)\sigma(n).
\end{aligned}
$$

Consequently, for a finite set S of primes and m=∏_{p∈S}p,

$$
\frac{KL(m)}{\sigma(m)}+\log2=\sum_{p\in S}f(p),\qquad
\log\frac{\sigma(m)}m=\sum_{p\in S}g(p).
$$

For p≥2, the two-point probability distributions
P=(1/(p+1), p/(p+1)) and Q=(1/p, (p−1)/p) have positive entries
and differ in their first coordinate. Their classical KL divergence
is f(p)−g(p), so `StrictGibbs.kl_divergence_pos_of_ne` gives δ(p)>0.
The upper estimate uses `FibonacciRankEulerTail.euler_log_bounds`;
together with the lower logarithm estimate it gives
2/(3p)≤f(p)≤2/p and 0<f(p)<log2. Prime reciprocal sums
therefore supply arbitrarily large finite tail sums of f, with
arbitrarily small individual terms.

Given B, choose a prime p>max(B,2), and let ε=δ(p)/2. Choose Q>p
so that f(q)<ε for every prime q>Q. Adjoin primes beyond Q to p
until the f sum first reaches log2. If S is the resulting set, then

$$
\log2\le\sum_{q\in S}f(q)<\log2+\varepsilon,
\qquad
\sum_{q\in S}g(q)
\le\sum_{q\in S}f(q)-\delta(p)<\log2.
$$

Thus m=∏_{q∈S}q is deficient and has KL(m)≥0. Among its positive
divisors with nonnegative KL, take the least d. Every proper divisor
of d is another divisor of m, so minimality gives KL-primitivity.
The divisibility monotonicity `GA2ForcedPrimeSource.abundancy_mono`
shows σ(d)/d≤σ(m)/m, so deficiency passes from m to d.
The sigma recurrence uses `ArithmeticFunction.isMultiplicative_sigma`
and `ReciprocalSigmaThreshold.sigma_prime`; its divisor-sum expression
uses `ArithmeticFunction.sigma_one_apply`.
Squarefreeness, oddness, and the lower bound B on every prime
factor also pass to d. Since KL(1)=−log2<0, d>1; a prime factor
of d exceeds B, so d>B. This gives the required unbounded family.

## Falsifier

The first threshold-crossing product need not itself be KL-primitive;
the least-divisor extraction is essential. That extraction may discard
the seed prime p, so unboundedness uses the lower bound on every prime
factor, rather than preservation of p. A non-strict Gibbs inequality
would not supply the positive margin needed for deficiency. The
definitions must retain the factor 2 inside the logarithm, the divisor
weight d, and all positive divisors, including 1. Zero is excluded from
the final family.

## Evidence

**Proved in Lean:**
`ZelinskyZhangKLPrimitive.result` proves
`∀ B : ℕ, ∃ n : ℕ, B < n ∧ 0 < n ∧ Deficient n ∧ KLPrimitive n`.
This is equivalent to infinitude, with positivity explicit.
The definitions of KL, deficiency, and KL-primitivity are those in
Equation (6), the source's abundancy terminology, and Definition 1.

**Proved on paper:** the normalization, strict local gap, finite
threshold crossing, and least-divisor extraction establish the stated
bounded-existence assertion. The prime-tail input is the established
divergence of the sum of prime reciprocals.

The literature assessment supplied with preregistration #31617 reports
no independent proof or refutation in its searches for the paper,
Conjecture 15, and deficient KL-primitive integers. The related
repository result is the refutation of Conjecture 22 in the same paper;
its divisor-weighted logarithmic sum differs from KL. This assessment
is limited to the reported searches and does not establish worldwide
priority.

## Triage

- **Proved in Lean: mechanism.** Dividing KL
  by σ converts adjoining a new prime into addition of f(p). The strict
  Gibbs gap f(p)−g(p)>0 leaves a fixed margin between the two thresholds;
  sufficiently small tail terms cross only the KL threshold.
- **Proved on paper; not separately formalized: strengthened form and
  question 2.** For every B there is an odd, squarefree, deficient
  KL-primitive integer whose every prime factor exceeds B. The same
  least-divisor construction retains these properties and gives d>B.
  In particular it answers the source's page-12 question 2 affirmatively:
  infinitely many odd integers are deficient and KL-primitive.
- **Proved in Lean elsewhere: question 1.** The source asks whether
  infinitely many integers are both primitive non-deficient and
  KL-primitive. The deficient family constructed here does not answer
  that question; `ZelinskyZhangDoublePrimitive.result` answers it
  affirmatively with integers 2^k p (see
  `Problems/zelinsky-zhang-2025-question-1.md`).
- **Proved on paper: relation to the source's 2^{k−1}p route.** Both
  routes obtain a deficient integer with nonnegative KL and then extract
  a KL-primitive divisor. The present squarefree construction uses many
  unrestricted large primes and a strict local gap; it requires no
  infinitude assertion for primes 2^k+1 or 2^k+3. It does not settle
  either of those prime-distribution assertions.

## ASSUMED-UNVERIFIED

Worldwide priority and completeness of subsequent literature remain
unverified. The supplied literature assessment is a bounded search
result. The strengthened odd, squarefree, large-prime-factor assertion
has a paper proof here; its separate Lean verification is not asserted.
