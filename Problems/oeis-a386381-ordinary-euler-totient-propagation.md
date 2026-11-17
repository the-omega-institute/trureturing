---
slug: oeis-a386381-ordinary-euler-totient-propagation
bibkey: kurkov2025a386381c2
doi: null
url: https://oeis.org/A386381/internal
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Periodic/EulerDivisorPropagation.divisor_propagation
  - D5/S1/Recurrence/Periodic/EulerDivisorPropagation.particular
---

# Ordinary Euler zero-divisor propagation

## Problem

For every k,m,d in Nat, d>2 and d|E(k) imply

`d | E(k + m*Nat.totient(d))`.

For every k,m in Nat with k!=3, the particular assertion is

`E(k) | E(k + m*Nat.totient(E(k)))`.

Here E is ordinary A000111 with offset zero and generating function
sec(x)+tan(x). It is not the modified diagonal of A386363. Both assertions
include m=0, and the first includes every even, odd, composite and
prime-power modulus greater than two. The second excludes only k=3.

## Motivation

This is the complete Conjecture 2 in A386381 revision 27. The source and
literature boundaries are in
[the Library note](../Library/RecurrenceComposition/kurkov2025a386381c2.md).
The preregistration is
[#31280](https://github.com/the-omega-institute/trureturing/issues/31280).
The intended resolution basis is the preregistered external open question;
Young's corrected congruence is a prior component, not a new result here.
No worldwide novelty or priority claim follows.

## Gap

The retained `D5/S1/Recurrence/Periodic/EulerDivisorPropagation.lean` proves
both assertions for the ordinary carrier supplied by
`D5/S1/Recurrence/Periodic/EulerTwoPrimary.lean`.
The intermediate theorem audits remain incomplete under the existing
[linked exception](https://github.com/the-omega-institute/trureturing/issues/31291).

## Route

Construct ordinary E by the positive A''=A*A' recurrence. Reconstruct the
integral derivatives A_b of 2 exp(bt)/(1+exp(2t)), b=0,1, and prove the
exact ordinary/sign correspondence. An odd-length finite geometric sum
identifies the coefficient after deleting p-divisible frequencies.
At every positive index the correction 1-epsilon*p^j is a unit modulo
p^r; unit-frequency powers have Euler period phi(p^r). Thus no early-index
valuation upper bound or eventual-period premise is needed.

The tangent convolution proves 2^s|E(2s+1); the secant convolution proves
E(2s) odd. For d>2 its totient is even. If 2^a divides d and m>0,
the shifted odd index is at least 2a+1, so the tangent bound handles the
two-primary part. Totient divisibility and prime-power divisibility
assemble the components in the same integer E value.

The m=0 case is the premise itself. The particular assertion uses
E(0)=E(1)=E(2)=1 and E(k)>2 for k>=4. Index three is excluded only there;
its m=1 instance fails because E(3)=2, phi(2)=1 and E(4)=5.

## Falsifier

A source-normalized k,m,d with d>2, d|E(k) and failure of the shifted
divisibility refutes the main assertion. A failure of the particular
assertion must have k!=3. An eventual-period failure, a weighted diagonal
or equality failure between nonzero residues is not such a falsifier.

## Evidence

The mathematical source declarations are `divisor_propagation` and
`particular` in `EulerDivisorPropagation`. Their Blueprint describes the
literal quantifiers and boundaries. Current compiled checks and axiom
closures are produced by the scoped canonical report; this dossier does
not duplicate machine status.

## Triage

- **Established:** The retained ordinary proof covers both complete source assertions: the all-modulus divisor propagation law and the particular family with only `k=3` excluded. Its mechanism is the ordinary signed correspondence, corrected odd-prime-power zero transfer, tangent two-primary divisibility, and prime-power assembly.
- **Boundary:** The result applies to the offset-zero ordinary A000111 carrier. It does not transfer to the weighted A386363 diagonal, to Conjecture 1, or to the separate A060818 assertion; those remain separate source targets.
- **Open:** The source dossier makes no claim about worldwide priority or exhaustive equivalent literature. Any extension beyond the two literal assertions, including stronger residue periodicity or a different carrier, requires a separate target and proof.

## ASSUMED-UNVERIFIED

Global priority, exhaustive present openness and uninspected equivalent
literature remain ASSUMED-UNVERIFIED. Conjecture 1 and the A060818
assertion are separate targets.
