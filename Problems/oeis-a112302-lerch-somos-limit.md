---
slug: oeis-a112302-lerch-somos-limit
bibkey: meijer2016a112302
doi: null
url: https://oeis.org/A112302
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/ComplementaryGoldenRatioLimit
---

# OEIS A112302: Meijer's Lerch recurrence limit

## Problem

Johannes W. Meijer's June 27, 2016 COMMENTS paragraph in OEIS A112302
states the exact external problem:

> With Phi(z, p, q) the Lerch transcendent, define LP(n) = (1/n) * sum(Phi(1/2, n-k, 1) * LP(k), k=0..n-1), with LP(0) = 1. Conjecture: Lim_{n -> infinity} LP(n) = A112302.

The proof retains all three registered definitions and the complete
four-conjunct theorem:

```lean
noncomputable def LerchKernel (s : ℕ) : ℝ :=
  ∑' j : ℕ, (1 / 2 : ℝ)^j / ((j : ℝ) + 1)^s

noncomputable def SomosConstant : ℝ :=
  Real.exp (∑' j : ℕ, Real.log ((j : ℝ) + 1) / (2 : ℝ)^(j + 1))

def LPSource (a : ℕ → ℝ) : Prop :=
  a 0 = 1 ∧ ∀ n : ℕ, 0 < n →
    a n = (1 / (n : ℝ)) *
      ∑ k : Fin n, LerchKernel (n - k.val) * a k.val

theorem result :
  (∀ s : ℕ, 0 < s →
    Summable (fun j : ℕ => (1 / 2 : ℝ)^j / ((j : ℝ) + 1)^s)) ∧
  Summable (fun j : ℕ => Real.log ((j : ℝ) + 1) / (2 : ℝ)^(j + 1)) ∧
  (∃! a : ℕ → ℝ, LPSource a) ∧
  (∀ a : ℕ → ℝ, LPSource a →
    Filter.Tendsto a Filter.atTop (nhds SomosConstant))
```

A112302 denotes the real Somos constant through its decimal expansion.
The kernel is Phi(1/2,s,1)=2 Li_s(1/2). For k in Fin n, n-k is positive;
the recurrence divides by n only under n>0. Both summability clauses and
unique source existence are part of the result, not assumed premises.

## Motivation

The fixed question is preregistered in
https://github.com/the-omega-institute/trureturing/issues/8050.
D5/S1/Recurrence/ComplementaryGoldenRatioLimit motivates studying recurrence
limits but concerns different complementary recurrences. It is context only,
not a direct frozen dependency or a premise for LP convergence.

## Gap

OEIS revision 121 still labels this LP limit a conjecture. The
exact proof addresses the entire registered statement. The mathematical
bridge is identification of LP with convergent coefficient partial sums,
followed by evaluation of their sum.

The evaluation identity is already known: D5/L/coffey2015somosseries,
Proposition 5(b), equation (1.25), at t=2 gives
sum_{k>=1}(2 Li_k(1/2)-1)/k = log(sigma_2).
That identity is not claimed as new and is not itself an LP-limit theorem.
The cited Somos product, logarithmic sum and nonlinear quadratic recurrence
likewise do not alone identify this linear convolution sequence.

## Route

The target address is D5/S1/Recurrence/LerchSomosLimit, generality I.
All auxiliary constructions and facts in the proof are local to
result; its only top-level mathematical declarations are the three
definitions and the single theorem above.

Write K_n=LerchKernel n. Geometric comparison proves kernel summability;
0<=log(j+1)<=j supplies a summable geometric-times-linear majorant for the
constant series. Nat.strongRec constructs the total source sequence, and
strong induction proves uniqueness from its exact initial value and recurrence.

For n>=1, removing the j=0 kernel term gives
r_n=K_n-1=sum_{j>=0}2^{-(j+1)}/(j+2)^n and 0<=r_n<=2^{-n}.
A second strong recursion constructs the nonnegative coefficients
c_0=1 and n*c_n=sum_{k=0}^{n-1}r_{k+1}*c_{n-1-k} for n>=1.
Induction gives 0<=c_n<=2^{-n}, hence absolute summability.
Finite-sum induction and index reflection show that
T_n=sum_{i=0}^n c_i satisfies LPSource. Uniqueness identifies T with LP,
so LP tends to sum_{n>=0}c_n without assuming a generating function.

For x in (-3/2,3/2), set H(x)=sum_{n>=0}c_n*x^n,
G(x)=sum_{n>=0}r_{n+1}*x^{n+1}/(n+1), and
B(x)=sum_{n>=0}r_{n+1}*x^n. The bounds by (3/4)^n and n*(3/4)^n
justify termwise differentiation. The absolutely convergent Cauchy product
and the coefficient recurrence give H'=B*H and G'=B.
Thus (H*exp(-G))'=0 throughout this connected interval. H(0)=1 and G(0)=0
give H(1)=exp(G(1)), identifying the coefficient sum.

To evaluate G(1), the double summand
2^{-(j+1)}/(j+2)^{n+1}/(n+1) is nonnegative and bounded by
2^{-(j+1)}*2^{-(n+1)}. Absolute summability permits exchanging the sums.
The logarithmic power series evaluates each j-row as
[log(j+2)-log(j+1)]/2^{j+1}. Summability permits the weighted telescoping
identity: with L_j=log(j+1)/2^{j+1}, the row is 2*L_{j+1}-L_j and L_0=0.
Consequently G(1)=sum_j L_j and H(1)=SomosConstant. This formally justified
evaluation realizes the known Coffey identity inside the LP proof.

## Falsifier

A positive real epsilon and an unbounded sequence of indices along which
a source sequence stays at least epsilon from SomosConstant would refute
the limit; a proved different limit would also refute it. Finite deviations
are insufficient. Failure of either summability claim or unique source
existence defeats the full registered statement. A prior exact published
LP settlement affects unresolved-target eligibility, not mathematical truth.

## Evidence

The complete OEIS revision-121 text is 6,191 bytes, SHA-256
`ed64c8e83d66f7f508c074805f27c16b379eb02e047c0be5cf0c22a12a830318`.
D5/L/meijer2016a112302 records the exact conjecture and constant-definition
locators; D5/L/weisstein2026lerch records the Lerch normalization.
D5/L/coffey2015somosseries records the original preprint's Proposition 5(b),
equation (1.25), and proof equations (2.19)--(2.26).

The canonical module compiles with the pinned Lean and Mathlib. A separate
verifier compiled the exact proof and a fresh checker expanding all three
definitions and all four conjuncts. The checker extracts an actual source,
checks n=1 and arbitrary positive n, positive predecessor exponents and
kernel summability, uniqueness, and the full real limit including its
all-sufficiently-large-indices epsilon formulation. Every authored
axiom closure is confined to propext, Classical.choice and Quot.sound.

The bounded independent source-check finding covers OEIS A112302
and related entries A274181, A090998 and A135002; MathWorld;
Sondow--Hadjicostas; Guillera--Sondow; and Coffey. It identifies the known
constant identity but no exact LP settlement in that inspected scope.
Chen--Han (2016) and Meijer--Baken (1987) full texts were inaccessible.
This is a bounded literature finding, not an exhaustive search or a global
priority claim. The preregistered repository, pinned Mathlib and third-party
Lean searches record no exact dominating LP theorem in their searched scope.

## Triage

First tier, fixed OEIS comment problem under #8050, with the explicit age
caveat that the conjecture dates from 2016 rather than 2024--2026.
`admission_basis: open-problem-resolution`. The per-declaration assessment is:

| Declaration | proof_shape | computational_content.kind |
| --- | --- | --- |
| LerchKernel | N/A (definition) | none |
| SomosConstant | N/A (definition) | none |
| LPSource | N/A (definition) | none |
| result | content | none |

For all four declarations, direct frozen dependencies: none;
`escape_witness: none`. The module imports only Mathlib. No separately
registered escape witness is claimed under this admission basis.
The theorem's content is the recurrence construction, coefficient bounds,
source identification and analytic convergence argument, not a new claim
to Coffey's constant identity. All declarations concern infinite real series
or an unbounded recurrence; none delivers bounded enumeration, a checker,
a numerical reduction or a certified finite instance. Other computational
utility fields are not-applicable(kind=none).

## ASSUMED-UNVERIFIED

Literature priority beyond the inspected scope is unverified, including the
two inaccessible full texts. Coffey's mathematical locator is the original
preprint; publisher coredata supports bibliographic identity, not inspection
of the journal version of record or its equation numbering. The Lerch note's
2026 year is its consultation year, not a verified first-publication date.
Excluded interpretations are a digit-valued limit, a kernel missing the
factor two, the nonlinear Somos recurrence as LP, and replacing the full
conjunction by a limit-only or conditional statement.
