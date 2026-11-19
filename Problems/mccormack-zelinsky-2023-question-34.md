---
slug: mccormack-zelinsky-2023-question-34
bibkey: mccormackzelinsky2023weightedamgm
doi: 10.48550/arXiv.2312.11661
url: https://arxiv.org/abs/2312.11661v4
triage: theorem
motivation_gids:
  - D5/S3/Arith/Abundancy/McCormackZelinskyQuestion34.result
---

# No odd pseudoperfect divisor set containing one has A greater than C

## Problem

McCormack and Zelinsky, arXiv:2312.11661v4, page 15:

> Question 34. Is there an odd primitive non-deficient n which is pseudoperfect with set S1, with 1 ∈ S1, and where A(S1, n) > C(S1, n)?

Their S1 is a subset of the positive divisors of n, possibly including n,
whose sum is 2n. Their example C({13,26,39,78},78) uses sum 156=2·78.
Equations (12) and (14), page 14, define

$$
A(S,n)=\sum_{d\in S}\frac{d}{2n}\log\varphi(d),\qquad
C(S,n)=\log\left(\sum_{d\in S}\frac{\varphi(n/d)}{2d}\right).
$$

Primitive non-deficiency means non-deficiency of n and deficiency of each
positive proper divisor. The formal existence statement retains oddness,
primitive non-deficiency, the divisor subset, membership of 1, sum 2n,
and the strict inequality C<A. Divisor complementation is exact natural
division. No closure under complementation is assumed.

## Motivation

The question tests whether an odd primitive non-deficient number can reverse
the weighted comparison when the divisor set contains 1. A universal
obstruction for odd divisor sets answers it independently of primitivity.

## Gap

Totient supermultiplicativity alone leaves a complementary logarithmic sum
whose lower bound must exceed 2 log 2. The bound must apply to arbitrary
divisor sets, including sets omitting some small complementary divisors.

## Route

Let T={n/d : d∈S}. Exact divisor complementation is injective and
the divisor sum gives

$$
\sum_{e\in T}\frac1e=2,\qquad
\sum_{\substack{e\in T\\e>1}}\frac1e\ge1.
$$

For odd e>1, totient below eight forces e∈{3,5,7,9}. On the other
indices log phi(e) is at least log 8. Allowing all four exceptions gives
the uniform lower bound

$$
\begin{aligned}
\sum_{e\in T}\frac{\log\varphi(e)}e
&\ge\frac{\log2}3+\frac{\log4}5
  +\left(\frac17+\frac19\right)\log6+\frac{67}{315}\log8\\
&=\frac{512\log2+80\log3}{315}>2\log2.
\end{aligned}
$$

The strict inequality follows from 9>8, so 2 log 3>3 log 2.
The exceptional coefficients are valid whether or not each exceptional
integer belongs to T: each missing integer removes a negative correction
to the baseline log 8.

For every d∈S, phi(d)phi(n/d)≤phi(n). Multiplication by d/(2n)
and summation therefore give

$$
A(S,n)\le\log\varphi(n)
  -\frac12\sum_{e\in T}\frac{\log\varphi(e)}e
  <\log\frac{\varphi(n)}2.
$$

The term d=1 contributes phi(n)/2 to the positive sum defining C.
There is another positive term, since S cannot be the singleton {1}
and have sum 2n. Hence C(S,n)>log(phi(n)/2), proving A<C.

## Falsifier

Replacing the sum 2n by n, assuming complementary closure, or omitting
membership of 1 changes the question. Logarithmic monotonicity requires
positive arguments. Separately optimized bounds for incompatible divisor
sets cannot be combined; the reciprocal mass and all corrections here
refer to the same set T.

## Evidence

The exact general statement is
`D5/S3/Arith/Abundancy/McCormackZelinskyQuestion34.odd_weight_reverse`.
It uses the existing `WeightedTotientEulerDensity.weightA` and `weightC`.
The existence claim uses the existing
`ZelinskyZhangDoublePrimitive.PrimitiveNonDeficient`.
The settling declaration `McCormackZelinskyQuestion34.result` has literal
type `¬ claim`; its `OpenProblemResolutionClaim` is **Refuted**.
The external problem settlement is preregistered in #31860.

Literature check (bounded): the fixed source version v4 still lists
Question 34 as open, and its Question 45 discussion gives no answer.
Searches of later preprints citing the source, the authors' subsequent
work and public repositories found no prior settlement. The repository's
Question 45 dossier lists Question 34 as not settled there.

## Triage

### What the settlement shows

- **Proved:**
  `D5/S3/Arith/Abundancy/McCormackZelinskyQuestion34.odd_weight_reverse`
  proves A<C for every odd divisor set containing 1 with sum 2n.
  Primitive non-deficiency is unnecessary for this stronger obstruction.
- **Proved:**
  `D5/S3/Arith/Abundancy/McCormackZelinskyQuestion34.result`
  refutes Question 34's existence claim. Its failure mechanism is the
  odd complementary-index lower bound, together with the positive
  contribution from d=1 in C.
- **Proved:** the same `odd_weight_reverse` gives the nearest surviving
  statement with the inequality reversed: every set satisfying Question
  34's other hypotheses satisfies A<C, hence also A≤C.
- **Computed:** oddness is essential. For even n the inequality can
  reverse with 1 in S: n=20 with S={1,4,5,10,20} has A-C≈0.066, and
  n=42 with S={1,6,14,21,42} has A-C≈0.324. Among the 1092 sets with
  1 in S and sum 2n for even n<400 with at most 16 divisors, 195 have
  A>C. The proof's lower bound has no even analogue: the index e=2
  has phi(e)=1 and contributes no logarithmic mass.
- **Proved (consequence):** the inequality clause of the source's D1
  condition holds for every odd n and every divisor set containing 1
  with sum 2n, by `odd_weight_reverse`. D1 itself additionally requires
  pseudoperfection, which is not decided here.
- **Computed (source example):** for odd n, sets omitting 1 can give
  A>C, as the source's n=1575 set shows; which odd n admit such sets
  is not classified here (**open**).
- **Open:** the source states no further result that depends on an
  answer to Question 34; the density statements of Questions 44 and 45
  are separate and are not changed by this settlement.

## ASSUMED-UNVERIFIED

Worldwide priority and exhaustive subsequent literature coverage are
unverified. The source statement and preregistration are supplied at the
fixed version above; no exhaustive literature certification is asserted.
