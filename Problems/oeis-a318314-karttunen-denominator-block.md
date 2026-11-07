---
slug: oeis-a318314-karttunen-denominator-block
bibkey: oeis2018a318314
doi: null
url: https://oeis.org/A318314/internal
triage: open
motivation_gids:
  - D5/S3/Arith/DirichletRoots/OeisA318314
---

# Karttunen's whole A318314 denominator block

## Problem

The exact published definition and conjectured block, with source versions,
attribution and CC BY-SA 4.0 notices, are retained in
[the source note](../Library/ArithUnits/oeis2018a318314.md).
For f(1)=1 and, for n>1,

$$f(n)=\frac{\operatorname{A068068}(n)-\sum_{d\mid n,\;1<d<n}f(d)f(n/d)}2,$$

put a(n)=den(f(n)), the positive reduced denominator, with den(0)=1. The question
is the entire conjunction a(n)=A006519(n) A317934(n), multiplicativity with
unit value, a(2^e)=2^A005187(e), a(p^e)=2^A011371(e) for odd primes p, and
 a(p^e)=2^(((2-A000035(p))*e)-A000120(e)) for all primes p.
Every positive n, every positive coprime pair and every natural exponent e,
including n=1 and e=0, is included. Multiplicativity of a is a conclusion.
Subtraction in the source exponent is ordinary integer subtraction.

A068068 counts positive odd unitary divisors. A006519 is the largest power of
two dividing n. A317934 independently prescribes a multiplicative function with
prime-power values 2^(e-s(e)). Here s is binary digit sum, A011371(e)=e-s(e),
A000035(p)=p mod 2, and T=A005187 has T(0)=0 and T(e)=e+T(floor(e/2)).

## Motivation

The recurrence is a rational Dirichlet square root. Its reduced denominator
requires a global no-cancellation argument: rational multiplicativity alone
does not establish multiplicativity of denominators.

## Gap

The Lean candidate separates the recurrence-defined f from an independently
constructed positive rational Euler product R. The remaining central bridge is
that the divisor convolution R*R equals the actual odd unitary divisor count
at every positive n, and therefore R satisfies the original recurrence.
Until that bridge is proved, the denominator formula for R is not a formula
for the actual a(n). The whole proposition `WholeBlock` remains unproved.

## Route

Write C(e)=binom(2e,e)/4^e. Chu-Vandermonde gives sum_{i+j=e} C(i)C(j)=1.
The series (1+x)B(x^2), with B(x)=sum C(e)x^e, has coefficients C(floor(e/2))
and squares to (1+x)/(1-x). Thus R uses C(v_2(n)) at two and C(floor(v_p(n)/2))
at odd primes. Factor the full divisor sum into these local convolutions and
identify the resulting product with the independently defined odd-unitary count.
Remove endpoint divisors and use positive-index uniqueness to obtain R=f.

Kummer's digit formula gives v_2(binom(2e,e))=s(e). Odd reduced numerators over
powers of two multiply without cross-cancellation. The global exponent is
v_2(n)+sum_{p|n}(v_p(n)-s(v_p(n))). Disjoint supports give multiplicativity;
the binary digit recurrence identifies T and verifies nonnegative integer
subtraction in all prime-parity cases.

## Falsifier

A counterexample is a positive integer violating any conjunct of the complete
published block, with f computed from its actual recurrence. A finite prefix,
a prime-power-only argument or a formula-defined denominator does not prove the
whole assertion. A defect in an intermediate Euler-product construction alone
would not refute the original question.

## Evidence

The source owner is `D5/S3/Arith/DirichletRoots/OeisA318314.lean`, with its
corresponding Blueprint Scribe. The prospective whole-question identity is
[unit #27584](https://github.com/the-omega-institute/trureturing/issues/27584),
whose unchanged preprobe statement is
[the preregistration](https://github.com/the-omega-institute/trureturing/issues/27584#issuecomment-6703336229).
The accepted ordinary proof covers the complete question. That proof is not
itself Lean evidence. No complete stronger source or duplicate owner was
located in the finite inspected scope; worldwide openness and novelty remain
unverified. The source note names the unread and bounded literature windows.

## Triage

Tier 1 external OEIS conjecture; the full Lean realization remains open.
This is one whole question, with no additional harder variant or second count.

### What the settlement shows

**Proved components:** `source_solution_unique` constructs the actual rational
recurrence and proves uniqueness at every positive index. `central_local_square`
and `central_denominator` establish the central local square and exact dyadic
reduction, with integer-subtraction correspondence. `local_denominators` includes
the halving recurrence, odd-prime exponent and all-prime parity formula for the
local factors. `root_structure` constructs a positive multiplicative rational
Euler product. `root_denominator` proves its global denominator product through
an odd-numerator invariant, not rational multiplicativity alone.

**Open:** Identifying R with the source recurrence, then concluding the entire
`WholeBlock` for a(n)=den(f(n)). The full-block proposition has no result theorem.
No global resolution is asserted by the proved local components.

**Computed:** No numerical experiment is used.

**Source consequences:** The proposed mechanism would make the entire conjectured
block a consequence of one global convolution bridge. Consequences for unrelated
OEIS claims, broader families and unread literature remain open; no neighboring
claim is added to this question.
