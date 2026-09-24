---
slug: wall-sun-sun-golden-unit-lift
bibkey: shi2026second
doi: 10.48550/arXiv.2603.25343
triage: wall
motivation_gids:
  - D5/S0/Carrier/Ring
  - D5/S0/Carrier/Conj
  - D5/S0/Carrier/Norm
  - D5/S0/Carrier/Units
  - D5/S1/Scale/Units
  - D5/S1/Scale/UnitGroup
  - D5/S1/Scale/Fibonacci
  - D5/S3/Arith/FibonacciRank
  - D5/S3/Arith/GoldenApparition
  - D5/S3/Arith/GoldenPrimeSplitting
  - D5/S3/Arith/GoldenPell
---

# Wall-Sun-Sun primes as a golden-unit lift problem

## Problem

Let `pi(m)` be the Pisano period, the least positive period of the Fibonacci
recurrence modulo `m`. The primary problem is whether there exists a prime `p`
with `pi(p) = pi(p^2)`. The stronger conjecture asserts that infinitely many
such primes exist.

Quoted from the introduction of arXiv:2603.25343v1:

> “A natural question was asked by Wall in his paper: Can there be a prime
> \(p\) such that \(\pi(p)=\pi(p^2)\)?”

> “It is known that up to \(10^{14}\), there are no such primes (cf. [16]).
> Still, using heuristics and probabilistic arguments, some authors conjecture
> the existence of infinitely many primes \(p\) satisfying
> \(\pi(p)=\pi(p^2)\) [7, 11].”

The same paper identifies the classical case with `d = 5` and reports that no
`WSS(5)` prime is known.

Candidate formal statements, after defining `pisanoPeriod`, are:

```text
Existence:  ∃ p : Nat, Nat.Prime p ∧ pisanoPeriod p = pisanoPeriod (p^2)
Stronger:   Set.Infinite {p | Nat.Prime p ∧ pisanoPeriod p = pisanoPeriod (p^2)}
```

The complete ordinary-mathematics development is maintained in
`docs/develop/theory/WALL_SUN_SUN_GOLDEN_UNIT_RESEARCH.md`. Its PH through GPC
sections constrain the problem and prove exact conditional, spectral, lattice,
and recurrence relations; they do not prove or refute WSS existence.

## Motivation

The frozen theorem in
`D5/S3/Arith/Lattices/PrimeCyclotomicTraceImage.lean` proves the exact image of
one prime cyclotomic trace map. It does not kernel-verify the broader
stable-rank, six-real-function, asymptotic, Gaussian-noise, complete-tower, or
golden-clock arguments in the theory volume.

The repository already contains the mod-`p` Fibonacci rank, golden apparition,
prime splitting, and Pell interfaces needed to state the first exact bridge.
The missing `p^2` lift is therefore a concrete boundary between the existing
frozen arithmetic and the global Wall question.

## Gap

- No frozen `pisanoPeriod` or recurrence-period API.
- `GoldenApparition` works modulo a prime; there is no golden algebra modulo
  `p^2` and no Hensel or p-adic order-lift theorem.
- There is no `p`-rational field or p-adic logarithm machinery.
- PID/UFD facts and the global unit classification do not decide the
  exceptional local lift.
- The exact cross-block reciprocity conditions retain depth parity but do not
  distinguish initial depth `1` from odd depth at least `3`.

## Route

1. Define the Fibonacci matrix `A = [[0,1],[1,1]]` over `ZMod m` and identify
   `pi(m)` with its multiplicative order.
2. Define the reduction of `GoldenInt` over `ZMod m` and identify multiplication
   by `phi` with `A`.
3. For `r = pi(p)`, express `A^r = I + pB (mod p^2)` and prove that period
   preservation is equivalent to `B = 0 (mod p)`.
4. Reduce the lift condition to Fibonacci and Lucas quotients in the split and
   inert cases, retaining the actual initial depth.
5. Connect those local conditions to the exact block clocks and reciprocity
   constraints in the theory volume without replacing exact order by density.

## Falsifier

The existential Wall question has no finite falsifier. A proof that no prime
can satisfy the equality would refute it; a proof of finiteness would refute
only the stronger infinitely-many conjecture.

The proposed bridge is finitely falsifiable: exhibit a prime for which the
direct pair period disagrees with the order of the Fibonacci matrix or golden
unit, or for which `A^pi(p) = I (mod p^2)` disagrees with
`pi(p^2) = pi(p)`.

## Evidence

For each tested prime, independent exact calculations must compare direct
pair-state periods, fast-doubling residues, and matrix exponentiation. Required
fields include `p`, `legendreSym 5 p`, `rank`, `pi_p`, `pi_p2`,
`F_r mod p^2`, `F_(r+1)-1 mod p^2`, and the agreement of all formulations.
Finite agreement validates the bridge only; it is not evidence that the global
existential statement is false.

## Triage

`wall`. The repository has substantial mod-`p` and exact-clock structure, but
the decisive `p` to `p^2` lift remains open.

## ASSUMED-UNVERIFIED

- Resolution status after arXiv:2603.25343v1 has not been rechecked for this
  relocation.
- The reduced golden-unit order must be proved to match the selected Pisano
  convention, including factors of two and small exceptional primes.
- Priority for repository-derived specializations is not claimed without a
  dedicated literature review.
