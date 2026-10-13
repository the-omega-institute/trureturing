---
slug: oeis-a361552-literal-partition-parity
bibkey: hanna2023a361552
doi: null
url: https://oeis.org/A361552
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Bilateral/HannaPentagonalPartitionParity
---

# The literal A361552 equation and ordinary partition parity

## Problem

Paul D. Hanna's OEIS A361552 revision #14 states:

> Conjecture: a(n)/2 == A000041(n-1) (mod 2) for n >= 1; that is, a(n) is even, and a(n)/2 has the same parity as the number of partitions of n-1, for n >= 1.

The original definition is:

> G.f. A(x) = Sum_{n>=0} a(n)*x^n satisfies the following. (1) 2*x = Sum_{n=-oo..+oo} x^(n*(3*n+1)/2) * (A(x)^(3*n) - 1/A(x)^(3*n+1)).

The source, attribution, immutable locator and classical suppliers are in
`Library/Recurrence/hanna2023a361552.md`. The preregistered exact question is
<https://github.com/the-omega-institute/trureturing/issues/16442>.

## Motivation

This is a first-tier externally published all-index conjecture from 2023.
The selected assertion concerns ordinary partition cardinality, including the
empty partition. It excludes the separate A359914 comparison.

## Gap

All original solutions are units of the ring `PowerSeries ℤ`.
`term A k` takes both powers in the unit group, with integer exponents
`3*k` and `-(3*k+1)`. `exponent k = pentagonal (-k)` is exactly the integer
`k*(3*k+1)/2`, with its nonnegativity and exact multiplication-by-two identity
included in `LiteralResolution`.

At coefficient degree `N`, `bilateral A` uses the interval `[-N,N]`.
The full-sum clauses prove each of the two unit-power monomials vanishes
outside that interval and that the complete integer-index family has sum
`bilateral A` in the coefficient topology. The window is therefore a full-sum
representation, not a finite-prefix replacement or a nonsummable default.

`Original A` states `bilateral A = 2*X` without assuming the constant
coefficient. The constructed `generatingUnit` supplies existence. The result
requires every original unit solution to have constant coefficient one and
to equal that constructed unit.

For every integer `n >= 1`, the coefficient is indexed by `n.toNat`.
The conclusion is integer divisibility by two and equality of the two integer
remainders modulo two after division by two. The partition index is
`(n-1).toNat`. The positive-index bridge proves
`n.toNat = (n-1).toNat + 1`; `a` is a signed-index coefficient function with
an explicit nonnegative-index correspondence. No evenness is asserted at zero.
`partitionCount 0 = 1` counts the unique empty partition.

## Route

Separate the index-zero term as `1-A⁻¹`. All other terms have positive
order. The original equation is equivalent to
`A⁻¹ = 1-2*X+nonzeroSum A`. Iterating its unit reciprocal improves agreement
by one coefficient. Stabilized coefficients construct an integral unit;
this construction does not use the desired congruence.

Ring homomorphisms preserve every unit power and each finite coefficient
window. Uniqueness in characteristic two identifies the reduction with one.
Integer coefficient division then constructs `halfSeries A` with
`A = 1+2*halfSeries A`.

Modulo four this unit squares to one. Reducing every integer power modulo
two gives the linearized terms. Multiplication by two removes the Euler
signs. The full-sum pentagonal supplier yields
`2*(halfSeries A*pentagonalSeries ℤ-X) = 0` modulo four.
The cancellation is performed as integer divisibility:
`4 | 2*c` implies `2 | c`. No cancellation of a nonunit occurs in `ZMod 4`.
The ordinary-partition product at predicate `True`, combined with Euler's
product and the geometric-factor inverse, gives
`pentagonalSeries ℤ * partitionSeries = 1`. Reduction modulo two and
coefficient comparison give the selected conjecture.

## Falsifier

An integer index `n >= 1` violating either parity clause would refute the
selected assertion. Failure of existence or uniqueness for the literal
integral-unit equation would invalidate its formal reading. An actual exact
prior resolution or other owner stops this target. An incomplete proof is
unresolved; finite computations and conditional statements do not close it.

## Evidence

The draft module has one newly authored public theorem, `result`, of type
`LiteralResolution`. Its internal helpers are used by that theorem.
The typed Blueprint presents the definitions and the entire assertion.
Guarded D5 and matching Reg compilation and the selected import-closure Lean
report have succeeded. The result's axiom closure is exactly `Classical.choice`,
`Quot.sound`, and `propext`. The Blueprint source supplies a typed clause echo;
its canonical render is part of the draft verification. These are checks by
the implementation worker, not independent pre-freeze approval.

The compiled DependentFamily mirror retains all original clauses, its exact
equivalence bridge, actual-positive law, rejected law, whole-family sensitivity
and observational dependence. Its raw-source occurrence selection is absent:
the inspector reports `declared_unresolved`, `source.selection_missing`, with
no binding certificate. The unfinished audit is disclosed under CLAUDE §3.9
in <https://github.com/the-omega-institute/trureturing/issues/16460>.
Unknown continuation does not assert undecidability. No freeze or publication
is implied by this dossier.

## Triage

**Proved in the draft:** `result : LiteralResolution` establishes the complete
literal integral-unit assertion, including nonvacuous existence, forced
constant coefficient one, uniqueness and parity at every integer index at
least one. The exponent and each monomial's support justify the full bilateral
sum in the formal coefficient topology. The first positive integer half is
odd because the ordinary empty-partition cardinality is one. At degree zero
the coefficient is one; there is no degree-zero evenness conclusion.

**Proved mechanism:** the index-zero term isolates the inverse unit, and every
nonzero summand contributes positive degree. The quotient-by-`X^d` comparison
therefore improves agreement by one degree and constructs the solution without
a parity premise. This existence/uniqueness construction and its consumed
helpers are proved for an arbitrary commutative coefficient ring. The stated
coefficient-half conclusion uses integral coefficients: characteristic-two
uniqueness proves evenness, characteristic-four unit powers linearize the
literal equation, and integer divisibility reduces to the ordinary-partition
reciprocal. Euler and ordinary-partition identities are classical suppliers;
no new Euler or partition method is claimed.

**Computed:** no finite-prefix or numerical experiment is used as evidence for
the conjecture. All-index symbolic proofs carry the mathematical conclusion.

**Settlement consequences and limits:** the draft proves the selected parity
statement for the unique original series, including the empty-partition case.
Its parity clauses imply the equivalent positive-degree mod-four coefficient
congruence. The separate A359914 comparison, asymptotic constants and unrelated
Hanna entries remain unresolved by this result. The immutable source contains
no further selected conclusion depending on this conjecture; no consequence
for an excluded question is asserted. Applicability is formal power series
and the product topology of coefficients, with no analytic-convergence premise.
The universal original equation is retained without an assumed existence,
initial coefficient, parity formula or counting bridge.

**Open delivery boundaries:** source-to-Lean fidelity still requires the
separately independent full-unit pre-freeze check. The Reg raw occurrence binding
is unfinished under issue 16460. Canonical freeze, admission, publication,
full gate, required CI, merge and dev verification are later obligations.
The bounded literature qualification does not establish global priority or
absence of private or unindexed resolutions.

## ASSUMED-UNVERIFIED

Global priority, private/unindexed work and exhaustive worldwide absence are
unverified. The bounded literature qualification and six planning proposals
are supplied evidence, not kernel axioms or independent implementation review.
Independent pre-freeze fidelity, deposit, full admission, publication, required
CI, merge and dev verification remain outside this draft stage.
