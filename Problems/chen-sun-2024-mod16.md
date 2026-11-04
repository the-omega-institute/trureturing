---
slug: chen-sun-2024-mod16
bibkey: chensun2024doublecharacters
doi: 10.48550/arXiv.2409.08213
url: https://arxiv.org/html/2409.08213v4#S1.E11
triage: theorem
motivation_gids:
  - D5/S3/Arith/CharacterSums/ChenSunOriginal.full_original
---

# Chen-Sun's full double-character sum modulo sixteen

## Problem

For every prime p>3 let n=(p-1)/2 and let d_p be the sum of
legendreSym(p,j*j+j*k) over both inclusive intervals 1<=j,k<=n.
Conjecture1.1(1.11) of arXiv:2409.08213v4 asks for the residues modulo16:
4(1-(-1)^((p-1)/8)), -2, p+1-(-1)^((h-1)/2)h, and
2-(-1)^((h-1)/2)h, for p=1,5,3,7 mod8 respectively.
The last two use the actual maximal-order ideal class number of Q(sqrt(-p)).

## Route and exact carriers

`ChenSunDoubleCharacter.doubleSum` preserves equation(1.8) literally, with
natural inclusive endpoints and integer Legendre values. The field in the
odd branches is `QuadraticOrderMaximal.PrimeImaginary.Field p`.
`maximalOrderEquiv` identifies its integral quadratic order with the actual
ring of integers; `sqrtFieldEquiv` identifies the field with Q(sqrt(-p));
`field_discr` proves discriminant -p. The value called h is exactly
`NumberField.classNumber` of that field. Its positivity is the Mathlib
class-number positivity theorem and its oddness is proved from the finite
character parity and the actual squared class-number bridge.

The finite part proves unrestricted prime-family energy congruences, using
restricted Gram correlation and a single factorial-product argument for both
parities. The analytic part proves genuine rational-prime Euler factors,
including2 and p, convergent zeta factorization, the actual L(1) residue,
and the squared functional equation at0 and1. No exact class-number identity
is introduced as an assumption. No arbitrary class-number parameter appears
in the final theorem. The original natural exponent (h-1)/2 is retained.

## Evidence and remaining delivery

The implementation is in draft PR26314. The complete all-prime four-branch
module and its actual import closure compile through the canonical scoped
build and report entries. The scoped report covers 39 project modules and
1,009 declarations, with only Classical.choice, Quot.sound and propext in
the complete project axiom closure. All 125 inventoried new public definitions
and theorems are present. Source and exact-statement seals are retained in the
native evidence bundle. Fresh independent formal review, required CI and
final delivery remain pending. There is no finite-prime cutoff, weakened
original, sorry, new axiom or native_decide implementation route.

The sealed full ordinary proof was independently approved. That review does
not certify Lean statement fidelity, novelty, priority, official acceptance
or unique credit. OriginalKPI remains0 until full reviewed delivery.

## Literature boundary

The bounded current screen described in the Library note found no exact
resolution. This is not an exhaustive negative literature assertion.
The original's [BS] is Borevich-Shafarevich. Existing L(0) Lean source retains
Yao Xu/cadamcat attribution through its existing Library note.

## Falsifier

An altered inclusive interval, a missing mod8 branch, a prime cutoff, a
nonactual h, or an unpaid class-number bridge invalidates this implementation
as an answer to the original. All four cases must be delivered together.

Four-slot escape registration is unfinished for the newly authored theorem
family, tracked in https://github.com/the-omega-institute/trureturing/issues/26321.
The source-specific realization, equivalence, variation, sensitivity and
observational-dependence proofs are not certified. No declared_validated status
is claimed. This audit debt is separate from native mathematical proof.
