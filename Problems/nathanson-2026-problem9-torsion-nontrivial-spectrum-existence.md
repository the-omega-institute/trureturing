---
slug: nathanson-2026-problem9-torsion-nontrivial-spectrum-existence
bibkey: nathanson2026sumintersections
doi: 10.48550/arXiv.2604.04781
url: https://arxiv.org/abs/2604.04781v2
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/GroupWords/NathansonProblem9.result
---

# Nathanson Problem 9: existence of a nontrivial proper spectrum

## Problem

Melvyn B. Nathanson, *Problems and results on intersections of product sets and sumsets in semigroups*, arXiv:2604.04781v2, Section 4, Problem 9, asks:

> Let G be an infinite torsion group. Describe the product intersection sets H_Q(G). Must there exist X in H_N^*(G) with X != {1} and X != N?

This dossier anchors exactly the final existence question. The preceding classification
request is outside its selected unit. The source uses N = {1,2,3,...}, ordered h-fold
products with repetitions, and H_N^*(G) for the spectra of asymptotically strictly decreasing
sequences of subsets of the same group G. Empty common intersections are allowed.

### Source correspondence

| Source clause | Canonical counterpart |
| --- | --- |
| Every infinite torsion group | `result` quantifies over `{G : Type u} [Group G] [Infinite G]`; it proves the statement for all infinite groups, so every torsion instance is included. |
| Arbitrary cardinality and group law | There is no `Countable G`, `CommGroup G`, bounded-exponent or subgroup assumption. |
| Positive-indexed subsets of G | `A : PNat → Set G`; `q+1` is positive successor. |
| Adjacent inclusion and infinitely many strict changes | `ASD A` is `(∀ q, A (q+1) ⊆ A q) ∧ {q | A q ≠ A (q+1)}.Infinite`. |
| Arbitrarily late strict changes | Infinitude of that subset of positive naturals implies `∀ q₀, ∃ q ≥ q₀, A (q+1) ≠ A q`; each constructed family is in fact strictly decreasing at every index. |
| Ordered h-fold products, repetitions allowed | Mathlib pointwise set multiplication and natural powers; both factor orders and all triple support and sign patterns are covered. |
| Core A and full positive spectrum | `spectrum A = {h : Nat | 0 < h ∧ (⋂ q, A q)^h = ⋂ q, (A q)^h}`. |
| X in H_N^*(G) | Take `X = spectrum A`; `ASD A` supplies the defining membership. |
| X differs from {1} and from N | Both inequalities in `result` concern the complete set `spectrum A`, with exponent zero excluded. |

The exact torsion-specialized, arbitrarily-late formulation is an application of this
single theorem and receives no additional retained theorem or resolution claim.

## Motivation

The question is a Tier-1 externally named existence problem, fixed before the proof at
https://github.com/the-omega-institute/trureturing/issues/21237#issuecomment-6390094250.
Its affirmative answer is `D5/S3/Combinatorics/GroupWords/NathansonProblem9.result`, with
`admission_basis: open-problem-resolution`. There is one selected unit and one Proved
`OpenProblemResolutionClaim`. Generalization from torsion groups to all infinite groups
does not add another unit.

## Gap

Infinite groups with no infinite-order element are not covered by the elementary
infinite-order cyclic construction. The cube-range dichotomy replaces any need to find
an infinite proper subgroup. The conclusion makes no attempt to describe all possible
product intersection spectra.

The source-faithful four-slot audit of `D5.S3.Combinatorics.GroupWords.NathansonProblem9.result`
is unfinished under https://github.com/the-omega-institute/trureturing/issues/21237.
The dependent-family realization preserves the complete universe-polymorphic group telescope
and uses the Boolean observation `decide (ASD A)` on the whole sequence state. Its equivalence,
actual-positive law, rejected whole-family intervention, sensitivity and actual observational
dependence have compiled proof terms. The producer classifies this registration as
`declared_unresolved`: `IE-C050 ClosedTruthReadout`, `reason=unclassified_form`,
`rule=source.unlinked_operand`, `site=Classical.choice; source_operand=Classical.choice`.
The missing evidence is an admissible source-linked readout closure and a validated
binding certificate. No Reg source is retained and no registration is claimed
`declared_validated`. The mathematical theorem remains unchanged.

## Route

If the cube range is finite, finite pigeonhole gives an infinite common-cube fibre.
On that fibre the square map is injective, since equal squares and equal cubes cancel
to equal roots. Ramsey thinning avoids every fixed mixed pair value in both orders;
squares avoid fixed values by injectivity. Singleton tails have empty core and empty
square-product intersection, while a common cube persists. Thus 2 is in the full spectrum
and 3 is outside it.

If the cube range is infinite, recursively choose cubes outside all earlier cube
inverse-orbits. Their roots have disjoint inverse-pairs. Ramsey thinning handles signed
mixed triples, using the coordinate that occurs once in each two- or three-point support.
Every pure signed triple equals one of x^3, x, inverse x, inverse(x^3); injectivity controls
those four values. Inverse-pair tails have empty core and empty cube-product intersection,
while the identity persists in every square-product set. Thus 3 is in the full spectrum
and 2 is outside it.

Countably many initial evaluations, rather than the whole ambient group, supply the
requirements for a nested Ramsey refinement. An increasing diagonal lies in each required
refinement on its entire tail. No element is chosen from an infinite intersection of
refinements. The licensed supplier is the relativized all-arity Ramsey theorem of
Yann Pequignot, at `b63066fd9f8075a30bc78d392405426bf084e226`; attribution, source pins,
compatibility substitutions, full license and retirement condition are in the source note.

## Falsifier

A counterexample would be an infinite torsion group for which every asymptotically
strictly decreasing sequence has spectrum {1} or all positive integers. The theorem's
quantifiers include that group and construct a family separating exponents 2 and 3,
so no such group satisfies the formal statement. Finite group or finite-tail tests alone
cannot settle this question.

## Evidence

The mathematical source is `D5/S3/Combinatorics/GroupWords/NathansonProblem9.lean`, with
matching Blueprint Scribe. The public declarations are the necessary definitions `ASD`
and `spectrum` and the single settling theorem `result`. All consumed construction and
supplier helpers are private. The unused `singleton_cancel`, the unused supplier
`infinite_ramsey_seq`, and the torsion-specialization wrapper are absent.

`result` has `proof_shape: content` after the same-delivery helpers are expanded to the
pinned upstream boundary. The live path includes the recursively constructed diagonal
with its entire-tail invariant and the recursively chosen disjoint cube inverse-orbits.
Conservative bind-only helpers organize cancellation, finite support cases, enumeration,
and spectrum separation; they supply no independent content credit. There are no direct
frozen D5 prerequisites. `utility: none` applies because the content is general infinite-group
mathematics, rather than finite enumeration, a checker, numerical reduction or a certified
finite instance. Source-faithfulness remains an independent content-review obligation.

## Triage

### What the settlement shows

| Item | Result and boundary |
| --- | --- |
| Final existence question in Problem 9 | Proved by `D5/S3/Combinatorics/GroupWords/NathansonProblem9.result`; one externally named unit. |
| All infinite groups | Proved by that same theorem; torsion is not required, and cardinality is unrestricted. |
| Decisive mechanism | Proved on the theorem's live path: cube-range dichotomy, cancellable support coordinates and countable Ramsey fusion. |
| Source's preceding spectrum classification | Open here; the proof only separates two exponents of a full spectrum. |
| Other source problems and stronger classifications | Open here; no additional resolution follows merely from this existence theorem. |
| Source theorems that precede Problem 9 | Their original statements are unchanged; this construction uses no conjectural source premise. |

### Literature status

The bounded repository and pinned-Mathlib search found no exact counterpart. The existing
Nathanson Problem 12 declaration treats integer-additive affine invariance. The source
screen distinguishes arXiv:2604.18869v2, whose advertised settlements concern Problems 10,
11 and parts of 4 and 7. The primary source, supplier and exact scope are documented in
`Library/ArithUnits/nathanson2026sumintersections.md`. These readings do not establish
exhaustive worldwide novelty.

## ASSUMED-UNVERIFIED

Exhaustive literature completeness and worldwide priority are ASSUMED-UNVERIFIED.
The four-slot audit remains unfinished under #21237 until its full compiled source-bound
evidence exists. Local proof verification, canonical freezing, independent review and
merged delivery are distinct obligations; a resolution claim alone does not establish them.
