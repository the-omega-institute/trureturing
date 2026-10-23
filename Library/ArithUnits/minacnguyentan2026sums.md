---
bibkey: minacnguyentan2026sums
authors: Ján Mináč, Tung T. Nguyen, Nguyen Duy Tân
year: 2026
title: Sums of units in finite rings and applications to Cayley graphs
doi: null
url: https://arxiv.org/abs/2607.00404v1
claim: Question 3.5 asks whether the exact n-sum property of a finite field transfers to every finite group algebra with units restricted by standard augmentation.
strata_touched:
  - D5/S3/ArithUnits/MinacNguyenTanQuestion35
license: CC-BY-4.0
triage: anchor
---

# Sums of units in finite rings

## Verified locator

The versioned record is https://arxiv.org/abs/2607.00404v1.
The primary question is https://arxiv.org/html/2607.00404v1#S3.Thmthm5.
Definition 3.1 defines an exact number of summands, with repetitions allowed.
The opening of Section 3 assumes a subgroup of units containing minus one.
Section 3.2 assumes a finite field of cardinality greater than two and at least
two summands, and defines the coefficient-sum augmentation on the actual group algebra.

## Question and scope

> Suppose that F has the n-sum property with respect to U. Is it true that F[G] also has the n-sum property with respect to U_{ε_G}?

Here G is an arbitrary finite group, U is a subgroup of F's multiplicative
units containing minus one, and U_{ε_G} consists of genuine group-algebra
units whose standard augmentation lies in U. The number of summands remains n.
Remark 3.6's n times the group order is a different, weaker conclusion.
Proposition 3.7 and Corollary 3.9 cover the modular p-group and nonmodular
cases, respectively; they do not settle the arbitrary-group question.

## Mathematical correspondence

The formal source uses `MonoidAlgebra F G`, its actual unit type, and
`MonoidAlgebra.lift` of the constant-one group homomorphism. This lift equals
the finite sum of coefficients. `augmentationUnitSubgroup` is the preimage
of U under the induced homomorphism of genuine unit groups.
`HasNSumProperty S n` quantifies over every ring element and a function on
`Fin n` whose values lie in S and whose sum equals that element.

The proof descends to the semisimple Jacobson quotient and uses its actual
Wedderburn matrix product. Orthogonal factor idempotents identify the factor
selected by augmentation. The selected simple factor injects into F, so its
entries are the prescribed scalar sums. Finite division rings are fields;
rank normal form and a scalar distinct from zero and one construct two
units in every remaining factor. Additional unit summands extend this to
the original n. Quotient-unit lifts remain units in the finite ring, and the
sum error lies in the radical and has zero augmentation. Adding that error
to one lift makes the sum exact without altering any augmentation.

## Literature boundary

The versioned source explicitly leaves the general case as Question 3.5.
The bounded exact-title, question-number, prescribed-augmentation and repository
search recorded in preregistration issue 15666 found no inspected prior
resolution. This is a bound on the inspected sources, not a claim of worldwide
absence. Classical matrix decomposition and radical lifting supply methods;
the source's Theorem 2.1 is not assumed as a Lean axiom.
