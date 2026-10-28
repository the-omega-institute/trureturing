# A collision of complete Pisano sets

## Abstract

The distinct integer seed pairs (0,1) and (1,1) have equal complete Pisano sets.

**Definition 1.1 (Integer Fibonacci seeds).**

Lean statement: `D5/S3/Arith/AndoyoPisanoSetCollision.F`

*Formalization.* `D5/S3/Arith/AndoyoPisanoSetCollision.F` (`✓ std3`).

*Citation.* Jason D. Andoyo (2026). *(a,b)-Fibonacci-Legendre Cordial Graphs and k-Pisano-Legendre Primes*. DOI: [10.62072/acm.2026.09011](https://doi.org/10.62072/acm.2026.09011). URL: <https://arxiv.org/html/2601.10561v1>.

*Commentary.*

For all integers a and b, F(a,b,0)=a, F(a,b,1)=b, and F(a,b,n+2)=F(a,b,n+1)+F(a,b,n). In particular the zeroth term is included.

**Definition 1.2 (Positive scalar periods).**

Lean statement: `D5/S3/Arith/AndoyoPisanoSetCollision.ScalarPeriod`

*Formalization.* `D5/S3/Arith/AndoyoPisanoSetCollision.ScalarPeriod` (`✓ std3`).

*Citation.* Jason D. Andoyo (2026). *(a,b)-Fibonacci-Legendre Cordial Graphs and k-Pisano-Legendre Primes*. DOI: [10.62072/acm.2026.09011](https://doi.org/10.62072/acm.2026.09011). URL: <https://arxiv.org/html/2601.10561v1>.

*Commentary.*

A natural t is a scalar period modulo p exactly when t>0 and, for every natural n including zero, the casts of F(a,b,n+t) and F(a,b,n) in ZMod p agree.

**Definition 1.3 (The least positive scalar period).**

Lean statement: `D5/S3/Arith/AndoyoPisanoSetCollision.pi`

*Formalization.* `D5/S3/Arith/AndoyoPisanoSetCollision.pi` (`✓ std3`).

*Citation.* Jason D. Andoyo (2026). *(a,b)-Fibonacci-Legendre Cordial Graphs and k-Pisano-Legendre Primes*. DOI: [10.62072/acm.2026.09011](https://doi.org/10.62072/acm.2026.09011). URL: <https://arxiv.org/html/2601.10561v1>.

*Commentary.*

The period is the natural infimum of the set of positive scalar periods. For the two seed pairs used in the theorem, finite invertible pair dynamics provides a positive period, and the infimum belongs to that set and is no larger than every member. Equality of the full positive-period predicates gives the same least positive period for the shifted pair.

**Definition 1.4 (Legendre counts with multiplicity).**

Lean statement: `D5/S3/Arith/AndoyoPisanoSetCollision.signCount`

*Formalization.* `D5/S3/Arith/AndoyoPisanoSetCollision.signCount` (`✓ std3`).

*Citation.* Jason D. Andoyo (2026). *(a,b)-Fibonacci-Legendre Cordial Graphs and k-Pisano-Legendre Primes*. DOI: [10.62072/acm.2026.09011](https://doi.org/10.62072/acm.2026.09011). URL: <https://arxiv.org/html/2601.10561v1>.

*Commentary.*

For a prime p and an integer sign s, count indices n in Finset.range(pi(p,a,b)) whose Legendre symbol legendreSym p (F(a,b,n)) equals s. This is an index set; repeated residue values contribute separately. The three signs used are 1, -1 and 0.

**Definition 1.5 (The integer Pisano-Legendre balance).**

Lean statement: `D5/S3/Arith/AndoyoPisanoSetCollision.K`

*Formalization.* `D5/S3/Arith/AndoyoPisanoSetCollision.K` (`✓ std3`).

*Citation.* Jason D. Andoyo (2026). *(a,b)-Fibonacci-Legendre Cordial Graphs and k-Pisano-Legendre Primes*. DOI: [10.62072/acm.2026.09011](https://doi.org/10.62072/acm.2026.09011). URL: <https://arxiv.org/html/2601.10561v1>.

*Commentary.*

Cast each of the three natural counts to the integers before subtracting: K=N(1)-N(-1)-N(0). The zero class is subtracted explicitly.

**Definition 1.6 (The complete Pisano set).**

Lean statement: `D5/S3/Arith/AndoyoPisanoSetCollision.chi`

*Formalization.* `D5/S3/Arith/AndoyoPisanoSetCollision.chi` (`✓ std3`).

*Citation.* Jason D. Andoyo (2026). *(a,b)-Fibonacci-Legendre Cordial Graphs and k-Pisano-Legendre Primes*. DOI: [10.62072/acm.2026.09011](https://doi.org/10.62072/acm.2026.09011). URL: <https://arxiv.org/html/2601.10561v1>.

*Commentary.*

For arbitrary integer a and b, chi(a,b) is the set of integers K(p,a,b) as p ranges over every prime different from two.

**Theorem 1.7 (An affirmative answer to Andoyo's Question 5.3).**

Lean statement: `D5/S3/Arith/AndoyoPisanoSetCollision.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/AndoyoPisanoSetCollision.result` (`✓ std3`). ∎

*Resolves.* `Problems/andoyo-2026-pisano-question-5-3` (proved) by `D5/S3/Arith/AndoyoPisanoSetCollision.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"andoyo-2026-pisano-question-5-3","declaration_gid":"D5/S3/Arith/AndoyoPisanoSetCollision.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jason D. Andoyo (2026). *(a,b)-Fibonacci-Legendre Cordial Graphs and k-Pisano-Legendre Primes*. DOI: [10.62072/acm.2026.09011](https://doi.org/10.62072/acm.2026.09011). URL: <https://arxiv.org/html/2601.10561v1>.

*Commentary.*

There exist integers a1,b1,a2,b2 with distinct ordered pairs, each different from (0,0), and chi(a1,b1)=chi(a2,b2). The proof supplies (0,1) and (1,1). There are no positivity, coprimality or phase-quotient hypotheses.

Write f(n)=F(0,1,n) and g(n)=F(1,1,n). The recurrence gives g(n)=f(n+1). A scalar period t of g fixes f(t+1) and f(t+2) modulo p; subtraction in the recurrence fixes f(t)=f(0). This recovers the zeroth index and proves equality of all positive scalar-period predicates. The original canonical period-return bridge and finite injective dynamics establish existence, and minimality gives the same least positive period T.

For each sign separately, let u(n) be its index indicator. The endpoint equality u(T)=u(0) makes the sum of u(n+1) over n<T equal the sum of u(n) over n<T, by cancelling the two expansions of the sum over n<T+1. This accounts for wraparound, repeated values and the zero class, with no T>1 premise. Equal integer balances for every same odd prime imply equality of the complete sets.

The source is Definitions 2.6 and 2.7 and Section 5, Question 5.3 of the cited preprint and journal article. The proof settles this existential question; it supplies no distribution or infinitude assertion for primes with a prescribed balance.

## References

- Truth anchor: `D5/S3/Arith/AndoyoPisanoSetCollision.F`
- Truth anchor: `D5/S3/Arith/AndoyoPisanoSetCollision.K`
- Truth anchor: `D5/S3/Arith/AndoyoPisanoSetCollision.ScalarPeriod`
- Truth anchor: `D5/S3/Arith/AndoyoPisanoSetCollision.chi`
- Truth anchor: `D5/S3/Arith/AndoyoPisanoSetCollision.pi`
- Truth anchor: `D5/S3/Arith/AndoyoPisanoSetCollision.result`
- Truth anchor: `D5/S3/Arith/AndoyoPisanoSetCollision.signCount`
- Dependency: [D5/S3/Arith/PisanoMatrixBridge](PisanoMatrixBridge.md)
