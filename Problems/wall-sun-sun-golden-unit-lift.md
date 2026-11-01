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
with `pi(p) = pi(p^2)`. The paper also records the stronger conjecture that
infinitely many such primes exist.

Quoted from the introduction of arXiv:2603.25343v1:

> “A natural question was asked by Wall in his paper: Can there be a prime
> \(p\) such that \(\pi(p)=\pi(p^2)\)?”

> “It is known that up to \(10^{14}\), there are no such primes (cf. [16]).
> Still, using heuristics and probabilistic arguments, some authors conjecture
> the existence of infinitely many primes \(p\) satisfying
> \(\pi(p)=\pi(p^2)\) [7, 11].”

The same paper identifies the classical case with `d = 5` and says there are no
known `WSS(5)` primes.

Candidate formal statement, after defining `pisanoPeriod`:

```text
Existence:  ∃ p : Nat, Nat.Prime p ∧ pisanoPeriod p = pisanoPeriod (p^2)
Stronger:   Set.Infinite {p | Nat.Prime p ∧ pisanoPeriod p = pisanoPeriod (p^2)}
```

The paper states the difficulty:

> “The question of Wall for these sequences is related to certain deep
> arithmetic properties of real quadratic fields.”

It makes this precise for its generalized recurrence: equality of the periods
modulo `p` and `p^2` corresponds, subject to stated hypotheses, to failure of
`p`-rationality of the associated real quadratic field. This is why the global
existence question is not a routine finite-period exercise.

## Motivation

- Multiplication by `phi` on the basis `(1, phi)` is the Fibonacci matrix.
  Frozen `Scale/Fibonacci` already expresses powers of `phi` in Fibonacci
  coordinates.
- `GoldenApparition` and `FibonacciRank` control the first Fibonacci zero modulo
  a prime and the `p ± 1` Frobenius index; `GoldenPrimeSplitting` supplies the
  split/inert division according to 5 modulo `p`.
- The period can therefore plausibly be re-expressed as an order of the reduced
  golden unit or Fibonacci matrix. Equality at `p` and `p^2` is then an
  exceptional failure of the usual order multiplication by `p` under lifting.
- The first reachable theorem is not existence. It is an exact bridge among the
  pair recurrence period, the order of the Fibonacci matrix, and the order of
  `phi` in an appropriate golden algebra modulo `p^e` for `e = 1, 2`.

## Gap

- `GoelPisanoRatioRefutation` already defines the frozen `pisanoPeriod` and proves the internal pair-period helpers. The new `PisanoMatrixBridge` theorem exposes the missing public bridge to the Fibonacci matrix order for every modulus `n > 1`.
- `GoldenApparition` works modulo a prime; there is no golden algebra modulo
  `p^2` and no Hensel or p-adic order-lift theorem.
- There is no `p`-rational field or p-adic logarithm machinery.
- PID/UFD facts and the global unit classification alone do not decide the
  exceptional local lift.

## Route

1. Use the public bridge `PisanoMatrixBridge.pisanoPeriod_eq_matrix_order` to identify
   `pi(m)` with the order of `[[1,1],[1,0]]` over `ZMod m`; its proof tracks
   `(F_n, F_{n+1})` through the reduced golden unit.
2. For `r = pi(p)`, write the first lift as `A^r = I + pB (mod p^2)`. Prove
   `pi(p^2) = pi(p)` if and only if `B = 0 (mod p)`, and that otherwise the
   period acquires the expected factor `p`.
3. Use the frozen split/inert and apparition results to reduce the required
   congruence to a Fibonacci/Lucas quotient modulo `p`, separately in the two
   Legendre-symbol cases.
4. Only after those bridge theorems exist should a theorist choose between a
   conditional nonexistence theorem for a prime class, a density heuristic, or
   the global Wall question. Do not jump from a finite scan to existence.

## Falsifier

The existential Wall question has no honest finite falsifier. A proof that no
prime can satisfy the equality would refute it; a proof of finiteness would
refute only the stronger infinitely-many conjecture.

The proposed bridge is finitely falsifiable: find a prime `p` for which the
directly computed pair period disagrees with the order of the Fibonacci
matrix/golden unit, or for which `A^pi(p) = I (mod p^2)` disagrees with
`pi(p^2) = pi(p)`.

## Evidence

Implement three independent exact calculations for every prime `p < 10^6`,
excluding and separately reporting ramified and small cases:

1. direct pair-state Pisano periods modulo `p` and `p^2`;
2. fast-doubling checks of `F_r mod p^2` and `F_{r+1}-1 mod p^2` at `r = pi(p)`;
3. matrix exponentiation of `A^r mod p^2` and the first-lift matrix `B mod p`.

Receipt fields should include `p`, `legendreSym 5 p`, `rank`, `pi_p`, `pi_p2`,
`F_r mod p^2`, `F_(r+1)-1 mod p^2`, and agreement of all three formulations.
This is bridge validation, not evidence that the global existential is false.

## Triage

`wall`. The repository is unusually close to the mod-`p` side, but the decisive
`p` to `p^2` lift is exactly the missing deep layer.

## ASSUMED-UNVERIFIED

- Whether the open problem was resolved after arXiv v1 is unverified; this
  records the paper's statement, not the entire later literature.
- The order of the reduced golden unit matches the chosen Pisano-period
  convention without a factor of 2 or a special case; that must be proved, not
  assumed.
- A useful local quotient criterion can be stated entirely with the current
  `GoldenInt` coordinate model.
- Any novelty of the proposed bridge lemmas is unassessed and belongs to the
  theorist's search step.

### PH. 固定黄金 Pell 曲线与初始 WSS 深度的高度预算

[Full argument, assumptions and unresolved boundaries](../Library/Arith/shi2026second.md#wss-ph).

### CG. 原黄金单位在连续、有限与整数几何中的同一缺陷

[Full argument, assumptions and unresolved boundaries](../Library/Arith/shi2026second.md#wss-cg).

### FPD. Recurrence-level square transport and maximal-prime descent

[Full argument, assumptions and unresolved boundaries](../Library/Arith/shi2026second.md#wss-fpd).

### THS. Exact theta sieving and the principal-orbit coefficient

[Full argument, assumptions and unresolved boundaries](../Library/notes/tanaka2026maass.md#wss-ths).

### ROC. Fixed-golden orders, mixed-conductor kernels, and zero-parameter dihedral forms

[Full argument, assumptions and unresolved boundaries](../Library/notes/tanaka2026maass.md#wss-roc).

### SGN. Spectral Galois arithmetic, exact congruence ideals, and packet norms

[Full argument, assumptions and unresolved boundaries](../Library/notes/tanaka2026maass.md#wss-sgn).

### STL. Saturated spectral trace lattices and exact loss under reduction

[Full argument, assumptions and unresolved boundaries](../Library/notes/tanaka2026maass.md#wss-stl).

### CTG. Complete-tower gluing and exact rational Eisenstein congruence depth

[Full argument, assumptions and unresolved boundaries](../Library/notes/tanaka2026maass.md#wss-ctg).

### HCR. One-prime Hecke reconstruction and the exact observable subfield

[Full argument, assumptions and unresolved boundaries](../Library/notes/tanaka2026maass.md#wss-hcr).

### SJC. Predictive completion of the original golden orbit at square precision

[Full argument, assumptions and unresolved boundaries](../Library/Arith/shi2026second.md#wss-sjc).

### TBN. A fixed-golden split tower and simultaneous initial-depth balances

[Full argument, assumptions and unresolved boundaries](../Library/Arith/shi2026second.md#wss-tbn).

### DCE. Primitive depth vectors from a solved exponential equation

[Full argument, assumptions and unresolved boundaries](../Library/Arith/shi2026second.md#wss-dce).

### GPC. Golden prime clocks, exact interlevel jets, and quadratic reciprocity

[Full argument, assumptions and unresolved boundaries](../Library/Arith/shi2026second.md#wss-gpc).

### CF. Carlitz degree-five exactness within the same Wieferich family

[Full argument, assumptions and unresolved boundaries](../Library/ArithUnits/niedbala2026carlitz.md#wss-cf).

### CX. Global characteristic support and two additional Carlitz families

[Full argument, assumptions and unresolved boundaries](../Library/ArithUnits/niedbala2026carlitz.md#wss-cx).

### PCL. Golden-clock sampling, prime-period coupling, and native block periods

[Full argument, assumptions and unresolved boundaries](../Library/Arith/shi2026second.md#wss-pcl).

### GCR. Cubic reciprocity on the original golden depth vectors

[Full argument, assumptions and unresolved boundaries](../Library/ArithUnits/dunn2024cubicreciprocity.md#wss-gcr).
