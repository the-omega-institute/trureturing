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

## Motivation

This dossier tracks the complete original Chen-Sun double-character-sum problem named by the declared D5/S3 arithmetic character-sums motivation. Its target is the full prime-family theorem with every residue branch and the actual imaginary-quadratic class number.

## Gap

The original conjecture is the full four-branch residue formula stated above. The draft candidate supplies a complete all-prime formal proof of that unchanged statement; no additional mathematical debt is asserted here. Remaining delivery and audit limits are recorded under Evidence, Triage, and ASSUMED-UNVERIFIED.

## Route

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

## Falsifier

An altered inclusive interval, a missing mod8 branch, a prime cutoff, a
nonactual h, or an unpaid class-number bridge invalidates this implementation
as an answer to the original. All four cases must be delivered together.

## Evidence

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

The bounded current screen described in the Library note found no exact
resolution. Independent terminal source audit has now closed the full-text
access gaps for arXiv:2606.03970v1 and arXiv:2606.22548v1 and found no full
prior resolution in the inspected theorems or proofs. This is bounded
evidence, not an exhaustive negative literature assertion. The original's [BS] is Borevich-Shafarevich. Existing L(0) Lean source retains
Yao Xu/cadamcat attribution through its existing Library note.

## Triage

This is a theorem candidate. Official run41763758525/current job126357803003
failed at candidate validation with `invalid-problem-candidate` because the
former `Route and exact carriers` heading was unknown to the closed dossier
schema; the tests-lean job succeeded. This source-only repair supplies the
eight required headings in canonical order. Canonical validation is left to
the owner after applying this artifact; it was not run here.

Fresh independent formal review, required CI, final merge, first-dev
synchronization, and four-slot escape registration remain pending. Four-slot
escape registration is tracked in
https://github.com/the-omega-institute/trureturing/issues/26321. The
source-specific realization, equivalence, variation, sensitivity and
observational-dependence proofs are not certified. No declared_validated
status is claimed.

## ASSUMED-UNVERIFIED

Priority is UNDETERMINED and OriginalKPI remains0. The bounded literature
evidence above does not establish universal novelty: author-maintained
updates, full forward citations, and differently phrased or unindexed
manuscripts remain unchecked. Official acceptance and final delivery remain
unverified until the owner applies this dossier and completes the required
review, CI, merge, first-dev and registration steps. This source-only
preparation did not rerun the native proof or canonical checks.
