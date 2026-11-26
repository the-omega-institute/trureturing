---
slug: zelinsky-zhang-2025-question-1
bibkey: zelinskyzhang2025klprimitive
doi: 10.48550/arXiv.2501.04209
url: https://arxiv.org/abs/2501.04209v2
triage: theorem
motivation_gids:
  - D5/S3/Arith/Abundancy/ZelinskyZhangDoublePrimitive.result
---

# Zelinsky–Zhang's two primitivities

## Problem

Zelinsky and Zhang, arXiv:2501.04209v2, page 12, question 1:

> Are there infinitely many n which are both primitive non-deficient and KL-primitive?

Page 2 defines primitive non-deficient integers as "non-deficient n with
no non-deficient divisors". Here divisors means positive proper divisors:
σ(n)≥2n and σ(d)<2d for every positive divisor d<n. Equation (6) defines

$$
KL(n)=\sum_{d\mid n}d\log\frac{d}{2\varphi(d)}.
$$

Definition 1 on page 12 requires KL(n)≥0 and KL(d)<0 for every positive
proper divisor d of n. The equivalent unbounded-existence assertion is

`∀ B : ℕ, ∃ n : ℕ, B < n ∧ 0 < n ∧ PrimitiveNonDeficient n ∧ KLPrimitive n`.

The explicit positivity condition excludes zero. The predicates use the same
σ, φ and real logarithm as the source.

## Motivation

The two primitivities require the first crossing of two distinct divisor
inequalities to occur at the same integer. Question 1 is the named external
problem in preregistration #31644. It concerns the non-deficient side,
whereas the same page's Conjecture 15 concerns deficient integers.

## Gap

A non-deficient integer with nonnegative KL need not be primitive for
either inequality. Taking its least divisor with nonnegative KL can
lose non-deficiency. A direct construction must control both signs at
all positive proper divisors while preserving unboundedness.

## Route

Let k≥3, put A=2^k, and choose a prime p with 3A/2≤p≤7A/4. Set n=Ap.
Since p is odd, the positive divisors of 2^a p have the forms 2^j and
2^j p, with 0≤j≤a. The exact formulas are

$$
\begin{aligned}
\sigma(2^a)&=2^{a+1}-1,\\
\sigma(2^a p)&=(2^{a+1}-1)(p+1),\\
KL(2^a)&=-\log 2,\\
KL(2^a p)&=-(p+1)\log 2+
 p(2^{a+1}-1)\log\frac p{p-1}.
\end{aligned}
$$

The Lean formulas for the mixed prime powers apply the existing
`ZelinskyZhangKLPrimitive.sig_prime_mul` and `kl_prime_mul` with n=2^a
and the odd prime p, using coprimality and the two pure-power formulas.
Only algebraic normalization remains; the mixed divisor sum is not
expanded independently.

Consequently σ(n)−2n=2A−p−1>0. A pure power of two is deficient.
For a proper divisor 2^a p, the exponent satisfies a<k, and
σ(2^a p)−2·2^a p=2^{a+1}−p−1<0. This establishes ordinary primitivity.

The strict logarithm bounds

$$
\frac1p<\log\frac p{p-1}<\frac1{p-1},
\qquad \frac23<\log2<1
$$

give KL(n)>2A−p−2≥A/4−2≥0. The first inequality remains strict
when k=3 and the final coarse bound is zero. KL(2^a p) increases with a,
so it suffices to bound the largest proper divisor containing p. At
m=2^{k−1}p,

$$
\frac{KL(m)}{p+1}
< -\log2+\frac{p(A-1)}{p^2-1}
< -\log2+\frac23<0.
$$

The middle inequality follows from
2(p²−1)−3p(A−1)=p(2p−3A)+3p−2>0. Together with KL(2^a)=−log2<0,
this controls every positive proper divisor, including 1.

The public theorem
`D5.S3.Arith.Robin.PriceRecord.FixedLayerRigidity.fixed_cardinality_prime_window`
with A=3/2, B=7/4 and N=1 supplies, for every sufficiently large real x,
a finite set of cardinality one whose member is prime and lies in
(3x/2,7x/4]. Nonemptiness supplies that prime. Taking x=2^k gives
unbounded n=2^k p, each with both primitivities. Both the prime-window
module and the present module have generality I.

## Falsifier

Every positive proper divisor must be checked for both inequalities;
checking only the integer or only the predecessor 2^{k−1}p without
justifying divisor classification and monotonicity would be insufficient.
The weight d and factor 2 inside the logarithm must remain those of
Equation (6). An infinitude assertion for primes at the exact endpoints
of the interval is unnecessary: the prime lies in the full fixed-ratio
interval. No least-divisor extraction is used.

## Evidence

**Proved in Lean:** `ZelinskyZhangDoublePrimitive.result` proves exactly
`∀ B : ℕ, ∃ n : ℕ, B < n ∧ 0 < n ∧ PrimitiveNonDeficient n ∧ KLPrimitive n`.
`PrimitiveNonDeficient` is non-deficiency together with deficiency of
every positive proper divisor. `Deficient`, `KL`, and `KLPrimitive` are
the existing definitions corresponding to the source's terminology,
Equation (6), and Definition 1. The unbounded-existence conclusion is
equivalent to infinitude of the positive integers with both properties.

**Proved on paper:** the displayed estimates establish the stronger
construction in which n is abundant and KL(n)>0, with both strict
negative proper-divisor conditions.

The literature assessment accompanying preregistration #31644 found no
answer to question 1 in its searches for the title, authors,
KL-primitivity, primitive non-deficiency, proofs and related literature.
The classical ordinary-primitivity classification is stated separately
below. The bounded literature assessment does not establish worldwide
priority or exhaust subsequent literature.

## Triage

- **Proved in Lean: question 1.** Positive integers satisfying both
  primitivities are unbounded, with every positive proper divisor tested.
- **Proved on paper: threshold mechanism.** The asymptotic lower ratio
  needed for the predecessor's KL negativity is 1/log2, while ordinary
  non-deficiency permits ratios below 2. Since 1/log2<2, a fixed-width
  interval fits between these thresholds. The choice [3/2,7/4] gives
  explicit rational margins. This asymptotic threshold description is
  not a separate Lean theorem.
- **Proved on paper; literature: ordinary classification.** For an odd
  prime p, the known equivalence is: 2^a p is primitive non-deficient
  exactly when 2^a<p≤2^{a+1}−1. See Joshua Zelinsky, *Must a Primitive
  Non-Deficient Number Always Have a Small Component?*, Journal of
  Integer Sequences 29 (2026), Article 26.4.3, page 4, Lemma 3.
  The classification is an established input, not a novelty claim.
- **Proved on paper: strict strengthening.** The constructed integers
  are abundant, σ(n)>2n, and satisfy KL(n)>0. The public Lean conclusion
  requires only non-deficiency and KL(n)≥0; no separately named Lean
  theorem for this stronger conclusion is asserted.
- **Proved in Lean; relation to the neighbouring problems.** Question 1
  is answered affirmatively by `ZelinskyZhangDoublePrimitive.result`.
  Every integer in this construction is even, so it supplies no odd
  family for question 2. Conjecture 15 is settled by the separate
  deficient construction `ZelinskyZhangKLPrimitive.result`; its odd,
  squarefree strengthening, which answers question 2, remains proved on
  paper and not separately formalized.
- **Unresolved: worldwide priority and exhaustive literature coverage.**
  The bounded search assessment supplies no proof of either claim.

## ASSUMED-UNVERIFIED

Worldwide priority and completeness of subsequent literature remain
unverified. The cited ordinary classification is a literature statement;
no separate Lean equivalence for the full classification is claimed.
The strict abundant and positive-KL strengthening has the paper proof
above; it is not asserted as a separate public Lean conclusion.
