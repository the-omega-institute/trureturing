---
bibkey: mishra2026finiterobin
authors: Challenger Mishra; Rahul Sarkar
year: 2026
title: "A finite arithmetic form of Robin's inequality and its equivalence to the Riemann hypothesis"
doi: null
url: https://arxiv.org/abs/2609.26787v1
claim: The preprint replaces the logarithmic factor in Robin's bound by a finite truncated exponential indexed by the number of distinct prime factors, proves the resulting stronger inequality in several classes, and proves equivalence with Robin's criterion; it does not prove RH.
strata_touched: []
license: citation-only
triage: anchor
---

# A finite arithmetic Robin criterion

The inspected source is [arXiv:2609.26787v1](https://arxiv.org/abs/2609.26787v1),
submitted 22 September 2026. This note records the stated theorem and its
interface to the FIB Robin route. It is a preprint report, not a new project
proof, Lean verification, or independent audit of every finite computation.

## The finite truncation

For $n>5040$, put $K=\omega(n)$ and

$$
 C_\omega(n)=e^\gamma\sum_{j=0}^{K}
       \frac{(\log\log\log n)^j}{j!}.
$$

The source calls

$$
 \frac{\sigma(n)}n<C_\omega(n)
 \tag{F}
$$

the $\omega$-inequality. Since the sum is a finite truncation of the
exponential at the same argument, (F) is pointwise stronger than Robin's
inequality in the source's range. The paper also studies the analogous
$\pi(n)$ truncation.

The source proves (F) for $\omega(n)\le 6$, for primorials, for square-free
integers, and for odd integers. Its minimal-counterexample analysis gives
that a counterexample to (F), if one exists, is superabundant; the paper also
derives multiplicity restrictions and proves $\omega(n)\ge21$ for a minimal
counterexample to the $\omega$-inequality.

## Equivalence boundary

Theorem 4 states that (F) for every $n>5040$ is equivalent to the Riemann
hypothesis. The paper then restricts the test to colossally abundant numbers
using the standard reduction from Robin's criterion. This is an equivalence:
neither direction supplies an unconditional proof of RH.

The proof's conditional direction uses Nicolas' estimate under RH, while the
unconditional structural direction reduces a hypothetical minimal failure to a
rigid superabundant configuration. Those reductions are useful search
interfaces, but they leave the same global strict inequality unresolved.

## Relation to the FIB encoding

The five-window labels `[null,2,3,2 5,5]` record local inclusion and do not
by themselves record the global distinct-prime count $\omega(n)$. A faithful
FIB application of (F) would therefore need an additional accumulated support
counter (or an equivalent source-preserving statistic), together with the
actual value of $\log\log\log n$. The local five-state recursion cannot be
declared to implement the truncated exponential merely because both systems
have finitely many labels.

This source supplies a non-duplicative target for the project: prove a
source-preserving map from a chosen FIB family to $(\sigma(n)/n,\omega(n))$,
or prove a uniform bound on the resulting truncated-exponential residual.
No such map or bound is currently established here, and the source does not
provide the missing signed Robin estimate for the FIB family.
