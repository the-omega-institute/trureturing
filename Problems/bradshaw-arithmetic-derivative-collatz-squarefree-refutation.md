---
slug: bradshaw-arithmetic-derivative-collatz-squarefree-refutation
bibkey: bradshaw2025collatz
doi: null
url: https://cs.uwaterloo.ca/journals/JIS/VOL28/Bradshaw/bradshaw3.pdf
triage: theorem
motivation_gids:
  - D5/S0/Certificates/BradshawConjectureTwentyRefutation.result
---

# Bradshaw's Conjecture 20

## Problem

Z. P. Bradshaw, *On a Family of Solutions to Arithmetic Differential
Equations Involving the Collatz Map*, Journal of Integer Sequences
28 (2025), Article 25.1.8, Conjecture 20, printed page 16:

> The solutions to the commutation problem D(C_{a,b}(n)) = C_{a,b}(D(n)) are squarefree for every a ≡ b (mod 2).

The same page defines `C(a,b,n) = (a*n+b)/2` for odd n and `n/2` for
even n. Printed page 3 defines `D : Nat -> Nat` by `D(0)=D(1)=0`,
`D(p)=1` at each prime, and `D(m*n)=D(m)*n+m*D(n)` for all m,n.
The closed formal claim quantifies over such D and all natural a,b,n,
with equal parity of a,b and `1 <= n`, and concludes `Squarefree n`
from the displayed commutation equality.

## Motivation

The frozen `BradshawConjectureTwentyRefutation.result : Not claim`
refutes the positive-input restriction of the source assertion.
At `(a,b,n)=(17,7,125)`, both sides equal 641, while `125=5^3`
is not squarefree. The source's five tested parameter pairs do not
include this pair.

## Gap

The bounded literature screen reported in
[issue 8643](https://github.com/the-omega-institute/trureturing/issues/8643)
located no prior resolution of Conjecture 20. The orchestrator's
arXiv conjunction query returned zero entries, with eleven entries
for the arithmetic-derivative positive control. Its OEIS query
returned A247583 and A383619, neither stating this resolution.
The citation-index gap and the unidentified citing-item lead remain
unresolved; this is not a claim of exhaustive literature coverage.

## Route

Construct an arithmetic derivative internally as
`D0(n) = sum (p,k) in n.factorization, k * NatDiv(n,p)`.
The empty factorizations give zero at zero and one. Prime
factorization of a product supplies Leibniz's rule, treating zero
factors separately. The four defining properties then give
`D(25)=10`, `D(125)=75`, `D(533)=54`, and `D(1066)=641`.
Since `C(17,7,125)=1066` and `C(17,7,75)=641`, the equality holds.
The prime square `5^2` divides 125, contradicting squarefreeness.

## Falsifier

A source restriction excluding positive odd parameters with b<a,
an incorrect interpretation of the two branches, or failure of the
arithmetic-derivative properties would invalidate source fidelity.
A prior published resolution of this exact conjecture would invalidate
open-problem-resolution eligibility without changing the counterexample.

## Evidence

The formal carrier is
`D5/S0/Certificates/BradshawConjectureTwentyRefutation.lean`.
Its public surface consists of `IsArithmeticDerivative`, `C`, `claim`,
and the sole theorem `result : Not claim`. The existence construction
and numerical deductions stay inside that proof. The Scribe result
node binds this dossier with `OpenProblemResolutionClaim(Refuted)`.
The kernel proof uses the standard three axioms and no `sorry` or
additional axiom. The source identity and printed locators are in
`Library/Certificates/bradshaw2025collatz.md`.

## Triage

Tier 1 external named conjecture, preregistered in issue 8643 before
the probe. The result has `proof_shape: bind-only`,
`escape_witness: null`, and `admission_basis: open-problem-resolution`.
Its computational use is a `certified-instance` with `basis=refutes`:
the result negates the closed claim. This dossier concerns only
Conjecture 20; Conjectures 17–19 about the standard Collatz map are
outside its scope.

## ASSUMED-UNVERIFIED

Source fidelity is a semantic review obligation, separate from kernel
verification. The extra hypothesis `1 <= n` makes claim weaker than
the printed conjecture, so its refutation refutes the source and
excludes the trivial n=0 solution. The intended parameter domain is
read as naturals of equal parity; the witness has positive odd a,b
with b<a, as in the source's five tested pairs.

Literature completeness is ASSUMED-UNVERIFIED. No citation index was
retrieved in full. A ChatGPT Pro literature seat reported a Google
Scholar search-index excerpt showing a citation-count-like value of 1
beside the article, but could not identify the citing item. That
unresolved lead does not establish either zero citations or a prior
resolution. The same seat reported that the author's earlier
ResearchGate preprint, publication/384084846, states the same
assertion as Conjecture 6 and gives no counterexample; these are
seat-reported literature readings.
