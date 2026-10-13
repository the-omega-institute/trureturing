---
slug: minac-nguyen-tan-question-3-5
bibkey: minacnguyentan2026sums
doi: null
url: https://arxiv.org/abs/2607.00404v1
triage: theorem
motivation_gids:
  - D5/S3/ArithUnits/Gardam
---

# Mináč–Nguyen–Tân Question 3.5

## Problem

The primary source is [Question 3.5](https://arxiv.org/html/2607.00404v1#S3.Thmthm5):

> Suppose that F has the n-sum property with respect to U. Is it true that F[G] also has the n-sum property with respect to U_{ε_G}?

The complete statement quantifies over a finite field F with more than two
elements, every finite group G, a subgroup U of F's units containing minus
one, and the original natural number n at least two. If every field element
is a sum of exactly n elements of U, every element of the actual group
algebra must be a sum of exactly n genuine units whose coefficient-sum
augmentations lie in U. Repetition is allowed. Modular characteristic,
noncommutative groups, characteristic two with more than two field elements,
and the trivial group remain in scope.

## Motivation

Gardam's group-ring work provides the repository's existing native group
algebra and genuine-unit context. This question concerns additive generation
with a fixed number of terms and a restriction on each augmentation.

## Gap

The paper proves several special cases and explicitly leaves arbitrary
finite groups unresolved. The bounded literature and repository search
associated with [preregistration 15666](https://github.com/the-omega-institute/trureturing/issues/15666)
found no inspected exact settlement. The first-tier source classification and
open-problem-resolution basis precede the Lean probe. No global priority
claim follows from that bounded search.

## Route

The standard augmentation kills the Jacobson radical. The semisimple quotient
is a product of finite matrix algebras. Its orthogonal factor idempotents
select a simple factor on which augmentation is an injective unital ring
map to F; that factor is identified with its scalar entries. The field
hypothesis supplies exactly n prescribed scalar summands there. Rank normal
form gives two-unit sums in every other factor, using a scalar distinct from
zero and one; adding unit summands gives exactly n terms. Units lift through
the nilpotent radical in the finite noncommutative ring. The lifting error
can be added to one summand while preserving unit status and augmentation.

## Evidence

`D5/S3/ArithUnits/MinacNguyenTanQuestion35.result` states precisely the
source transfer using `MonoidAlgebra`, genuine units, and the standard
augmentation. The result Describe carries `OpenProblemResolutionClaim(Proved)`.
The one result uses proof-local arguments; there are no companion theorems,
private mathematical helpers, or wrapper results.

The source-specific [unfinished-audit issue 15686](https://github.com/the-omega-institute/trureturing/issues/15686)
records the missing producer-accepted source binding and registration. The
retained `Reg/D5/S3/ArithUnits/MinacNguyenTanQuestion35.lean` compiles the
complete family, bridge, variation, sensitivity and dependence, including
`F = ULift (ZMod 3)`, `G = ULift Unit`, `U = ⊤`, `n = 2` and a
bottom-subgroup counterreadout. The attempted descriptor was rejected with
producer exit 2 and
`contract.discovery:rigid_universes:Reg.D5.S3.ArithUnits.MinacNguyenTanQuestion35.registration_1`.
There is no `declared_validated` registration; the linked-issue route leaves
the audit unfinished.

## Falsifier

A mismatch in the native group-algebra or unit definitions, loss of a
modular or noncommutative case, a changed number of terms, failure to preserve
individual augmentations, or a nonstandard axiom would invalidate this
settlement. A result restricted to coprime characteristic, abelian or solvable
groups, or n times the group order would not settle the question.

## Triage

This is a first-tier externally named problem with admission basis
`open-problem-resolution`. The mathematical unit is general and contains no
bounded enumeration, checker, numeric reduction, or certified finite instance;
its utility classification is `none`. Independent review, source-author audit
completion or its linked-issue exception, canonical freeze, required checks,
and integration are separate delivery obligations.

The author classifies the compiled proof as `content`, pending independent
review. Preregistration 15666 anticipated `bind-only`; the original exact
question was preregistered, not the content classification. The admission
basis remains `open-problem-resolution`.

## ASSUMED-UNVERIFIED

The literature search is limited to the versioned primary source and the
bounded web and repository scope identified above. It does not establish
worldwide absence of a prior proof. No resolution status is handwritten here;
the canonical theorem and Scribe binding carry the mathematical result.
