---
slug: adamson-explicit-graph-outside-g2
bibkey: adamson2026twoword
doi: null
url: https://arxiv.org/abs/2605.27183v1
triage: theorem
motivation_gids:
  - D5/S0/Diagonal/PigeonholeFiber
---

# An explicit membership graph outside G₂

## Problem

The source is the unnumbered request in the conclusion of the paper identified
by `adamson2026twoword` in the Library. Its literal wording is:

> We did not find an example of a graph G such that G ∉ G₂. By Remark 30 we know that such a graph exists. Finding such a graph remains an open problem.

Let V = Fin 24 ⊕ Finset (Fin 24). The candidate U₂₄ has an edge from inl a to
inr S exactly when a ∈ S, the same adjacency in reverse, and no within-part
edges. Its endpoint states that there do not exist lists w,v over V such that
(∀ z : V, count z w = 2), (∀ z : V, count z v = 2), and
∀ x,y : V, x ≠ y → (U₂₄.Adj x y ↔ filter (z = x ∨ z = y) w =
filter (z = x ∨ z = y) v). These are Definitions 1 and 14 at k = 2.
Positive counts give the full vertex set as the alphabet of both words.

## Motivation

This Tier-1 external question asks for an explicit graph, whereas Remark 30
already gives nonconstructive existence. It is separate from Conjecture 31,
which asks for strictness of every hierarchy inclusion. The source imposes
neither connectedness nor minimum size; inr ∅ is permitted to be isolated.
The literal membership formula specifies the graph without any ordering or
search over graphs. Its vertex count is 24 + 2²⁴ = 16,777,240.

## Gap

The escape content is reconstruction
for arbitrary words from the ordered A-restriction and A-prefix cuts at each
occurrence of a B-letter. The statement must permit tied cuts and different
A-orders in w,v. Count identities, membership extensionality, finite
cardinalities and the numerical inequality are ordinary prerequisites, not
new named results or independent escape witnesses.

## Route

Delete B-letters from each word. The resulting lists each have length 48.
The two occurrences of each subset S give two cuts in {0,...,48} per word,
so a pair of words assigns S a signature in (Fin 49 × Fin 49)².
The recursive cut definition scans the actual word; reconstruction inserts
unit markers at those cuts and then projects onto a and the unit marker.
Renaming the marker to S gives exactly the original a/S projection.

The frozen `D5/S0/Diagonal/PigeonholeFiber.finite_reading_has_fiber`, applied
directly to the signature map, gives distinct S,T with equal signatures:
49⁴ = 5,764,801 < 16,777,216 = 2²⁴. Reconstruction is applied separately
to w and v. Injectivity of the unit-marker renaming transfers projection
equality between S and T, so their neighborhoods into A coincide. In the
membership graph, finite-set extensionality then forces S = T, a contradiction.
No equality of the two A-restrictions is assumed.

## Falsifier

A representation satisfying all displayed quantifiers would contradict the
endpoint. A weaker projection convention, omitted vertex occurrence condition,
extra word-order assumption or unproved encoding bridge would invalidate
identification with the source request. The construction does not answer
minimum-size, connectedness or strict-hierarchy variants.

## Evidence

The source PDF was read at Definitions 1 and 14, Remark 30, Conjecture 31 and
the conclusion. Its SHA-256 is
`f978a9e9de5cfaf8adfba59125cf16293b17f6b969f5f72594eab7a0cec719ca`.
The formal declarations are `projection_eq_reconstruction` and
`u24_not_in_g2` in `D5/S1/Words/GraphRepresentation/ExplicitNonTwoUniform.lean`;
the corresponding Scribe source supplies their mathematical mirror.

The frozen pigeonhole dependency has statement identity
`sha256:5f55169af7d89edac5921dbfefa1ae643783901e94726f4763079e1c068f4b6f`.
Pinned List count/filter/map/length APIs and Fintype cardinalities supply the
ordinary steps. The supplied scoped D5, Mathlib and third-party intake found
no exact reconstruction or explicit G₂ obstruction theorem. This is a scoped
reuse conclusion, not a claim that every prerequisite was absent upstream.

## Triage

`theorem` is the route classification. Both named theorems have proposed `proof_shape: content` and
`admission_basis: escape-witness`; the live reconstruction is the escape
step. No bind-only exception is used. `utility: none` describes an unbounded
structural argument, not enumeration, a checker, a numerical reduction or
a computed positive finite instance.

## ASSUMED-UNVERIFIED

The caller's September 15, 2026 checks found only v1 and no exact published
explicit answer in the searched exact-title and neighborhood-complexity
results. The latter search is weak negative evidence. Related checked source
sections concern global counting, unrestricted copy languages or different
union/alternation notions. Worldwide priority remains `ASSUMED-UNVERIFIED`.
The candidate is `suspected-novel` only within that search scope; Scribe
records the proof as repository-derived and acknowledges the source question.
