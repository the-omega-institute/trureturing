---
slug: bastien-khormali-link-irregular-tournaments
bibkey: bastienkhormali2025digraphs
doi: null
url: https://arxiv.org/abs/2512.20494v1
triage: theorem
motivation_gids:
  - D5/S3/ConceptDynamics/GraphIrregularity/LinkIrregularTournamentExistence.result
---

# Bastien–Khormali link-irregular tournament existence

## Problem

Alexander Bastien and Omid Khormali, *On Link-irregular Digraphs*,
[arXiv:2512.20494v1](https://arxiv.org/abs/2512.20494v1), Conjecture 6,
assert that a link-irregular tournament exists on `n` vertices if and only
if `n >= 6`. The precise resolution here is its nonvacuous reading:

```lean
∀ n : Nat, 2 ≤ n →
  ((∃ R : Fin n → Fin n → Prop, IsTournament R ∧ LinkIrregular R) ↔ 6 ≤ n)
```

`IsTournament R` requires irreflexivity and exactly one directed edge between
each two distinct vertices. `DirectedLink R v` is `Subrel R` on the carrier
`{w // R v w ∨ R w v}`, the union of the out- and in-neighbors.
`LinkIrregular R` requires `IsEmpty (DirectedLink R u ≃r DirectedLink R v)`
for every two distinct vertices `u` and `v`. Thus the isomorphisms excluded
are arbitrary bijections preserving and reflecting the directed relation.
In a tournament the neighbor union is exactly the complement of the vertex,
so these links are the actual vertex-deleted directed tournaments.

The restriction `2 ≤ n` is essential. At orders zero and one the pairwise
condition is vacuous and a tournament exists, while `6 ≤ n` is false.
The result does not prove the literal unrestricted equivalence at those
orders. It proves both directions for every order in the stated domain.

## Motivation

This is a first-tier recent small conjecture, preregistered in
[issue #8571](https://github.com/the-omega-institute/trureturing/issues/8571).
The independent question is the exact existence threshold for the source's
directed-link notion, including the negative orders two through five.
The source proves the assertion through order eight and reports
computational verification through order 100. The all-order theorem goes
beyond that reported finite verification.

## Gap

The primary source contains no all-order proof. The relevant prior-art
inspection includes the complete 2010 Belkhechine–Boudabbous paper and the
1993 Schmerl–Trotter source: its page 198 definition of the classical W
family was verified and its statements inspected, with imperfect OCR
elsewhere in the PDF. No exact all-order link-irregular tournament theorem
was located in these inspected materials. This is a bounded literature
finding, not a claim of worldwide priority or exhaustive historical openness.

The existing Library notes record the source and the classical inputs:

- [Bastien–Khormali](../Library/ConceptDynamics/bastienkhormali2025digraphs.md):
  Conjecture 6, the exact order-six arcs, and the reported finite range.
- [Schmerl–Trotter](../Library/ConceptDynamics/schmerltrotter1993critical.md):
  the classical odd-order family `T_r^(3)`, also denoted W.
- [Belkhechine–Boudabbous](../Library/ConceptDynamics/belkhechineboudabbous2010indecomposable.md):
  the W definition and related deletion and surviving-pair arguments.

The all-order gap is addressed by `result`. Its construction uses the
classical family and a sink extension; neither a new family nor a new
general method is claimed.

## Route

For orders two through five, classify the smaller deletion cards up to
actual permutations. Their orders one through four have respectively one,
one, two, and four tournament isomorphism classes. Pigeonhole therefore
forces two of the original tournament's deletion cards to be isomorphic.

At order six, use exactly the source's fifteen one-based arcs:
`(1,6), (1,3), (1,4), (2,1), (3,2), (3,4), (3,6), (4,5), (4,6),
(4,2), (5,1), (5,2), (5,3), (5,6), (6,2)`.
The proof checks this tournament and excludes all directed card
isomorphisms inside the Lean kernel.

For odd `n ≥ 7`, use the classical W tournament: a transitive chain with
one pivot pointing to the even zero-based chain labels and receiving arcs
from the odd labels. For even `n ≥ 8`, add a sink to the preceding odd-order
W. This yields the same alternating-pivot description; the even-order
extension is not asserted to be a classical critically indecomposable W.

Inside each chain-deleted card, the pivot is uniquely characterized by
the property that its further deletion leaves a transitive tournament.
For any other further deletion, one of three disjoint adjacent chain pairs
survives together with the pivot and gives a directed triangle. Every
isomorphism between two chain-deleted cards must consequently preserve the
pivot. Finite chain-rank rigidity then fixes the ranks of the remaining
chain. At the smaller deleted rank, the corresponding vertices in the two
cards have opposite pivot-edge parity, a contradiction. Finally, deleting
the pivot gives a transitive card, whereas every chain-deleted card is
nontransitive. The proof transports these card arguments to `DirectedLink`
through actual `RelIso` maps; no numerical invariant or restricted
isomorphism class substitutes for the source definition.

## Falsifier

A link-irregular tournament of order two, three, four, or five, or an order
`n ≥ 6` admitting no such tournament, would contradict the displayed
equivalence. A directed isomorphism between two distinct deletion cards of
the given constructions would invalidate the existence proof. A mismatch
between the source's neighbor union or directed isomorphisms and the Lean
definitions would invalidate the source-to-formal resolution claim even
if the Lean theorem remained true. Orders zero and one are explicitly
excluded, not counterexamples to the displayed theorem.

## Evidence

The formal source is
[LinkIrregularTournamentExistence.lean](../D5/S3/ConceptDynamics/GraphIrregularity/LinkIrregularTournamentExistence.lean).
Its declaration surface is exactly the three definitions `IsTournament`,
`DirectedLink`, `LinkIrregular`, and the canonical theorem `result`.
All construction and finite-classification arguments are internal to that
theorem; the conclusion quantifies over every natural order `n ≥ 2`.

The authoritative module membership is the
[frozen state](../Golden/Frozen/state/D5/S3/ConceptDynamics/GraphIrregularity/LinkIrregularTournamentExistence.lean.json).
The [Freeze event](../Golden/Frozen/accepted/b27d04f87d1a8f27cc723e63f79ca5e69acbddb05a9df88e3323e57515c8be35.json)
records the module statement identity and the separate declaration identities,
including `result`. Its prerequisite frozen-node list is empty; the formal
imports are from pinned Mathlib. The
[Scribe source](../Blueprint/D5/S3/ConceptDynamics/GraphIrregularity/LinkIrregularTournamentExistence.scribe.cs)
attaches `OpenProblemResolutionClaim` with `ResolutionKind.Proved` to that
exact theorem and this dossier's slug, retaining all three Library references.

## Triage

`theorem`; the typed `Proved` claim concerns Conjecture 6 on the explicitly
nonvacuous domain `n ≥ 2`. The assessment is `proof_shape: content`,
`utility: none`, and `admission_basis: open-problem-resolution` under the
preregistration in issue #8571. The public conclusion is obtained by an
unbounded construction and card-isomorphism argument. The three definitions
specify its general relational model; the theorem's internal small-order
computations do not constitute separate delivered finite instances, a
checker, or a numerical reduction. These classification and admission
assessments remain subject to independent semantic review.

## ASSUMED-UNVERIFIED

Source-to-Lean fidelity, proof-shape classification, utility classification,
and the admission assessment are semantic obligations, not consequences of
the frozen hash alone. Independent final review remains required.
The prior-art scope above excludes an all-order proof in the inspected
materials; it does not exclude an uninspected publication, unpublished
solution, or a passage obscured by the 1993 PDF's imperfect OCR.
Universal literature completeness and world priority are unverified and
are not claimed. Final canonical Scribe emission, repository checks, and
public CI for this dossier and typed claim remain the caller's obligations.
