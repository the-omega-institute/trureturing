---
slug: oeis-a397315-three-row-blackout
bibkey: pemmasani2026blackouts
doi: null
url: https://github.com/apemm/Kagey-Problems/blob/b9567e4dc1c7cf1e5034569571a9479b1b83dc57/kagey-problems/problem001/paper/main.tex
triage: theorem
motivation_gids:
  - D5/S0/Observation/FiniteWindowCRTIndistinguishability
---

# OEIS A397315: the Three-Row blackout conjecture

## Problem

Arjun Pemmasani's Three-Row conjecture states that the maximum number of
points that can be blacked out in a three-row grid with m columns, while
every lattice rectangle remains identifiable, is m+2 for every m>=3.
The exact source definitions and complete target are:

```lean
def IsRectangle {m : ℕ} (C : Finset (Fin m × Fin 3)) : Prop :=
  C.card = 4 ∧
  ∃ a b c d : Fin m × Fin 3,
    C = {a, b, c, d} ∧
    (((b.1.val : ℤ) - (a.1.val : ℤ)) *
        ((c.1.val : ℤ) - (a.1.val : ℤ)) +
      ((b.2.val : ℤ) - (a.2.val : ℤ)) *
        ((c.2.val : ℤ) - (a.2.val : ℤ)) = 0) ∧
    (a.1.val : ℤ) + (d.1.val : ℤ) =
      (b.1.val : ℤ) + (c.1.val : ℤ) ∧
    (a.2.val : ℤ) + (d.2.val : ℤ) =
      (b.2.val : ℤ) + (c.2.val : ℤ)

def ValidBlackout {m : ℕ} (S : Finset (Fin m × Fin 3)) : Prop :=
  ∀ C D : Finset (Fin m × Fin 3),
    IsRectangle C → IsRectangle D → C \ S = D \ S → C = D

theorem result :
  ∀ m : ℕ, 3 ≤ m →
    (∃ S : Finset (Fin m × Fin 3),
      ValidBlackout S ∧ S.card = m + 2) ∧
    (∀ S : Finset (Fin m × Fin 3),
      ValidBlackout S → S.card ≤ m + 2)
```

The first coordinate is column and the second row. Translating both
coordinates by one identifies this grid with the source convention.
The parallelogram equations and perpendicular adjacent vectors describe
Euclidean rectangles; four distinct corners exclude degeneracy. Squares
and tilted rectangles are included. Rectangle identity is equality of
unordered corner sets. Empty presentations are allowed. The result gives
both an attaining valid blackout and the matching bound on every valid
blackout, for every natural width at least three.

## Motivation

The exact external assertion was publicly preregistered in
https://github.com/the-omega-institute/trureturing/issues/8066 at
2026-09-15T09:19:42Z, before every numerical or Lean probe. The registration
discloses the earlier unverified row-pair counting direction; it does not
claim to precede every mathematical thought.

D5/S0/Observation/FiniteWindowCRTIndistinguishability supplies context for
questions about what finite observations distinguish. Its CRT statement
concerns a different observation map and supplies no premise for this
geometric result. It is not a direct frozen dependency.

## Gap

OEIS revision 38 and the pinned preliminary note both label the complete
three-row assertion a conjecture. The known two-row Strip Theorem and
difference-set/hitting-set equivalence do not themselves supply the full
three-row theorem. Neither finite agreement nor an axis-only result is a
replacement for the registered two-sided, all-width statement.

## Route

The canonical address is
D5/S0/FiniteGeometry/RectangleIdentifiability/ThreeRowBlackoutMaximum,
generality I. FiniteGeometry is a foundational domain for finite lattice
point configurations and shape identifiability; the only imports are
pinned Mathlib. All new proof helpers are local to result. Only the two
necessary source definitions and the single complete result are delivered.

The proof first establishes the known geometric classification recorded
by Hector J. Partridge in OEIS A289832 (D5/L/partridge2017a289832). A
rectangle is either axis aligned or a unit diamond occupying three
consecutive columns. The classification follows from the integer
orthogonality and parallelogram equations with three possible row
coordinates; it does not assume an exhaustive rectangle generator.

For attainment, black out the entire boundary row and boundary column.
Their overlap is counted once, so this set has m+2 points. Ordering the
columns of axis rectangles and treating the possible row pairs gives
injectivity for two axis rectangles. Visible corners distinguish an axis
rectangle from a diamond and distinguish different diamonds. This proves
validity for the complete rectangle family, not just axis rectangles.

For the upper bound, validity on all rectangles implies validity on the
axis rectangles used in the collision argument. No two distinct columns
can black out the same pair of rows: the width hypothesis supplies a
third column that would give colliding presentations. This is the cited
two-row Strip Theorem obstruction, proved locally here.

There is also a cross-pair obstruction. If columns p,q,r black out row
pairs 01,02,12 respectively, comparing the appropriate two axis
rectangles forces q=r. Let A,B,C be the sets of blacked-out columns in
rows zero, one and two. The two obstructions give
card(A intersection B)+card((A union B) intersection C)<=2.
Two applications of finite-set inclusion-exclusion, together with
card(A union B union C)<=m, bound the blackout size by m+2.

## Falsifier

A genuinely valid blackout with more than m+2 points for any m>=3 would
refute the bound; a proved strictly smaller maximum would refute
attainment. Any claimed counterexample must use the full registered
rectangle family and presentation convention. Failure to find a proof
is not a refutation or a proof of independence. A known exact prior
settlement changes unresolved-target eligibility, not mathematical truth.

## Evidence

D5/L/pemmasani2026blackouts records the complete original OEIS revision
and preliminary-note locators, hashes, attribution and source conflicts.
D5/L/partridge2017a289832 attributes the known oblique-rectangle
classification; its complete original entry was read and its hash checked.
The complete preregistration has SHA-256
`d0a19de054e503bbfe3b53007ee2c55c79cca49342515643f9b7147c8c3a81fb`.
The Stage A source was produced after that public registration and
compiled with the pinned Lean and Mathlib, with no warnings or errors.
It retains the two definitions and full theorem signature verbatim.
An independent mirror compiled the exact standalone source and a fresh
checker expanding both predicates at every occurrence of the complete
result. It independently verified all 56 emitted source declarations,
including 53 compiler-generated theorem auxiliaries, against only
propext, Classical.choice and Quot.sound. It also checked a tilted square,
a nonsquare axis rectangle, duplicate-corner exclusion and the uniqueness
of a fully hidden rectangle under valid blackout.

The canonical source compiles without warnings under the pinned Lean and
Mathlib. Root's separate fresh checker verifies the fully expanded
geometry and entire two-sided result, extracts a witness for arbitrary
m>=3, applies the upper bound to an arbitrary valid S, and checks all 56
canonical module constants through Lean.collectAxioms. These are local
kernel checks; semantic source faithfulness is also independently reviewed.

An independent source-only audit read the complete original note,
upstream Lean file and named original sources and found no exact all-width
Three-Row settlement in that inspected scope. The complete original Kagey
question, A085582/A289832/A399580 entries, upstream README and PROBLEM.md,
and the 2017 triangular-array Stack Exchange question and sole answer were
also inspected. The latter concerns equilateral triangles, a different
shape family. Numerical claims and diagrams are not proof premises.

Ordered theorem searches covered repository D5, pinned Mathlib, then
available external Lean search. Loogle's blackout query and bounded
GitHub repository queries located no exact target. Fresh all-state
repository ownership queries for A397315, Pemmasani and blackout returned
zero indexed records at 2026-09-15T09:18:58Z, each with
incomplete_results=false. These are bounded search findings, not global
absence or exclusive-ownership guarantees.

## Triage

First tier, the fixed recent source-labelled conjecture in issue #8066.
`admission_basis: open-problem-resolution`; `escape_witness: none`.

| Declaration | proof_shape | computational_content.kind |
| --- | --- | --- |
| IsRectangle | N/A (definition) | none |
| ValidBlackout | N/A (definition) | none |
| result | content | none |

All three declarations have no direct frozen dependencies. The result
proves unbounded geometric classification, an actual uniform attaining
construction and a structural collision/counting bound. It does not
deliver a bounded enumeration, a checker, a numerical reduction or a
certified finite instance. Finite row case analysis supports the general
proof. Other computational utility fields are not-applicable(kind=none).
No separately registered escape witness is claimed.

## ASSUMED-UNVERIFIED

Eligibility is limited to the inspected sources. Exact-source web queries
encountered inaccessible, challenged or query-relaxed responses, which
supply no negative evidence. The two lattice-rectangle-counting papers
linked by A085582, arXiv:2604.22456 and 2607.17961, were not inspected in
full; their titles do not exclude a relevant theorem. No exhaustive
literature or global-priority claim is made.

Source numerical verification, the five-by-five diagram and the broader
Excess-1 conjecture are outside this result. No upstream Lean source is
copied: no license was located and its toolchain differs. The result is
not an axis-only theorem, a two-row theorem, a finite table, a conditional
upper bound or an attainment-only assertion.
