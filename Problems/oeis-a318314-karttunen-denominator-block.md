---
slug: oeis-a318314-karttunen-denominator-block
bibkey: oeis2018a318314
doi: null
url: https://oeis.org/A318314/internal
triage: theorem
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

The recurrence-defined f is separate from the independently constructed rational
Euler product R. The theorem `root_square` identifies its full Dirichlet square
with the actual odd-unitary-divisor count, and `root_source` proves SourceSpec R
and R(n)=f(n) for every positive n. The theorem `whole_block : WholeBlock`
then establishes the entire original event for a(n)=den(f(n)).

This source result does not assert worldwide novelty, completed audit
registration, independent prefreeze approval or delivered Frozen membership.

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

Tier 1 external OEIS question, with the whole Lean source result `whole_block`.
This is one whole question, with no additional harder variant or second count.

### What the settlement shows

**Proved:** `whole_block : WholeBlock` covers the source specification and
positive-index uniqueness, the product identity at every positive integer,
a(1)=1, multiplicativity at every positive coprime pair, both prime-power types
and the all-prime parity/digit-sum formula with its ordinary-integer subtraction
identity. All exponents include zero. No premise assumes multiplicativity of a.

The live bridges are `root_square`, identifying the global Dirichlet square
with the actual filtered divisor count, and `root_source`, identifying the
independent product with the recurrence. The helper `source_convolution` is an
equivalence for every rational function u, with no constraint at zero. The
no-cancellation proof `root_denominator` uses odd reduced numerators over dyadic
denominators; multiplicativity of rational values alone is not used to infer
denominator multiplicativity. `auxiliary_structure` verifies the independently
prescribed A317934, and `local_denominators` retains all integer-cast obligations.

**Open:** Source-owner audit bindings and independent statement/form/mirror
approval remain unfinished. Kernel compilation of the whole source is distinct
from freeze, required-check success, protected delivery and resolution counting.

**Audit boundary:** Source-owner four-slot registrations remain unfinished under
[issue #27596](https://github.com/the-omega-institute/trureturing/issues/27596).
The typed recurrence, global-square, source-identification and whole-block
families are statement-specific registration attempts; their source selectors
and binding evidence remain unfinished. They do not provide registration for
the other component statements. No `declared_validated` status is asserted.

**Computed:** No numerical experiment is used.

**Source consequences:** The global convolution and uniqueness bridges make the
entire conjectured block a theorem about the actual recurrence. Consequences for unrelated
OEIS claims, broader families and unread literature remain open; no neighboring
claim is added to this question.
