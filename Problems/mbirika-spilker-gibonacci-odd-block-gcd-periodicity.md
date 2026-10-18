---
slug: mbirika-spilker-gibonacci-odd-block-gcd-periodicity
bibkey: mbirikaspilker2023oddgcd
doi: null
url: https://arxiv.org/abs/2204.12626v2
triage: theorem
motivation_gids:
  - D5/S3/Arith/FibonacciAtomic/Windows/OddBlockGcdPeriodicity.result
---

# Joint odd-length periodicity of Gibonacci window gcds

## Problem

Mbirika-Spilker, arXiv:2204.12626v2, Question 6.4, asks:

> Under what conditions on the initial values G_0 and G_1 are
> G_{G_0,G_1}(k) and G^2_{G_0,G_1}(k) periodic on odd k values?

Both gcds range over every natural shift t of the actual sums of
`G(t+1),...,G(t+k)` and their squares. The recurrence has arbitrary
integer initial values a,b. The primitive convention is justified by
scaling; it is not a positivity condition. Example 6.3 uses periodicity
for every odd k starting at one, rather than eventual periodicity.

## Motivation

The two infinite families have different finite-gcd representations.
One joint period must work for both original families at every positive
odd length, including signed and nonprimitive seeds.

## Gap

The linear component and the finite modular-state method are prior in
Chen-Pan. Guyer-Mbirika gives the linear finite formula; Mbirika-Spilker
gives the square finite formula, scaling and odd fixed cap. The remaining
composition connects the genuine all-shift square family with a complete
modular-state return and obtains the simultaneous endpoint. A finite
bound on gcd values alone supplies no period.

## Route

Use the existing Fibonacci step `(x,y) -> (y,x+y)` on integer pairs.
The actual linear windows obey an order-two recurrence in t, and the
square windows obey an order-three recurrence. These give universal
integer-divisor specifications from the first two and three windows.
Telescoping reduces a length change to endpoint residues.

The alternating quadratic invariant `Q(x,y)=y^2-xy-x^2` gives the common
odd cap `M=2|Q(a,b)|`. The golden norm characterization proves that M is
positive for every nonzero seed pair. The existing complete-state return
modulo M supplies `R=(M^2)!`. A length change of 2R preserves parity and
both window families modulo M. Their universal specifications and the
caps give mutual gcd divisibility and hence equality.

## Falsifier

A nonzero integer seed pair for which no common positive period exists
for the two genuine odd-length gcd sequences would contradict the result.
A finite-shift replacement, eventual-only period, or omitted sign or
scaling case would fail to answer the source question.

## Evidence

`D5/S3/Arith/FibonacciAtomic/Windows/OddBlockGcdPeriodicity.result` states
the initial values and recurrence, uniqueness against every sequence with
those data, the two all-natural-shift specifications for every integer
divisor, signed scaling, the joint positive odd-index period from zero,
and the normalized zero-seed clause. The period is existential and is
not claimed to be least.

The reused public results are
`D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.result` for complete
modular-state return and `D5/S0/Carrier/Euclidean.norm_eq_zero_iff`
for the zero-invariant boundary.

## Triage

`theorem`: every source-allowed primitive pair satisfies the requested
joint periodicity, and the theorem also covers every nonzero integer
pair without coprimality or sign restrictions. The all-zero pair has
the separately labeled normalized extension.

### What the settlement shows

The decisive mechanism is a common nonzero odd cap combined with an
invertible modular state, with exact infinite-gcd specifications providing
the final equality. These statements and the scaling extension are
proved by the result named above. The construction needs no division by
the gcd of the seeds. It changes none of the source's finite formulas
or even-length results.

Least periods, effective bounds improving the factorial witness, and
the higher-power question in Section 6.1 remain open here. They are not
additional consequences asserted by this result.

## ASSUMED-UNVERIFIED

First-publication priority is not established. The bounded supplied
comparison and the directly checked primary formulas do not exclude
equivalent whole coverage in Spilker's inaccessible generalized chapter
of 2016. The linear periodicity component and the modular method are
explicitly attributed to Chen-Pan and are not claimed as new methods.
