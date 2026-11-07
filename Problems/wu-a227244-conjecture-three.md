---
slug: wu-a227244-conjecture-three
bibkey: wu2026a227244c3
doi: null
url: https://oeis.org/A227244/internal
triage: theorem
motivation_gids:
  - D5/S3/Arith/Primes/WuA227244ConjectureThree.result
---

## Problem

Chai Wah Wu's OEIS A227244 Conjecture 3 states:
"Conjecture 3: a(72*n+32) = 149 for n >= 0 and a(72*n+32) is not covered by Conjectures 1 and 2."
The source and license are in [wu2026a227244c3](../Library/Factorization/wu2026a227244c3.md).
The named external question is [#27415](https://github.com/the-omega-institute/trureturing/issues/27415).

The result preserves the disclosed progression-index CONDITIONAL interpretation,
not an author-written quantified formula or established author intent.
For each natural n, two independent hypotheses exclude membership of 72*n+32
in 20*k+16 and 220*k+8, respectively. Each existential k ranges separately over
all natural numbers, including zero. The conclusion is conditional on both
hypotheses; it does not assert unconditional noncoverage.

## Statement echo

| Clause | Canonical counterpart |
| --- | --- |
| All n>=0, including zero, unbounded | forall n : Nat |
| C1 progression noncoverage | not exists k : Nat, 72*n+32=20*k+16 |
| Independently, C2 progression noncoverage | not exists k : Nat, 72*n+32=220*k+8 |
| Exact signed integer | G(m)=((2:Int)^(2^m)+1)*2^(2^(2^m))-1 |
| Least prime divisor 149 | 149 is prime, divides G(72*n+32), and every natural prime divisor q of that same integer satisfies 149<=q |

Exponents are natural; the product and subtraction are integer operations.
There are no additional exclusions, finite bounds or eventual-onset assumptions.

## Motivation and route

The result determines the least prime divisor throughout an unbounded conditional
family. Progression periodicity and a tail-period transfer reduce the nested
powers to finite residues. The first noncoverage hypothesis yields n mod 5 != 2,
which excludes 101; the second yields n mod 55 != 18, which excludes 47.
Divisibility by 149 and nonzero residues for every one of the 34 smaller primes
complete the least-prime argument. Both bridges are used in the proof.

## Falsifier

An n satisfying both independent noncoverage hypotheses with failure of
divisibility by 149, or a natural prime q<149 dividing the same signed integer,
would refute this precise conditional assertion.

## Triage

| Item | Result and boundary |
| --- | --- |
| Conditional C3 | The canonical result retains the complete stated conditional family. |
| Interpretation | Progression-index noncoverage is disclosed; author intent is not established. |
| General method and priority | No new general method, escape witness or global priority claim. |
| Literature | No exact supplier on the bounded checked surfaces; completeness remains unverified. |

## ASSUMED-UNVERIFIED

Global literature completeness and priority are unverified. The four-slot audit
is unfinished under [the linked exception](https://github.com/the-omega-institute/trureturing/issues/27415#issuecomment-6706796802).
The dependent-family source candidate is uncompiled. Exact reconstruction,
equivalence/realization, variation/sensitivity, observational dependence and
current enrolled-template binding evidence are missing. No declared_validated
status is claimed.
