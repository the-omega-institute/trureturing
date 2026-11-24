/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SparseCocycleSupport
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SparseCocycleSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Finset.Powerset]
   utility: none
   digest: Sparse pivot graphs force triple support of order nine or twelve. -/

import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Interval.Finset.Nat

/-! The sparse graph support step for Hong–Wu–Xia Problem 2.

An edge lies in four triples. An adjacent edge rules out a single-edge triple
by prescribing an outside vertex. The cap of two requires at least two
distinct such vertices. With three edges this gives a three-spoke
star, since a triangle repeats the outside vertex. With four edges a
degree-three center would leave a fourth edge with at most one such vertex.
At maximum degree two, every edge must have another edge at both ends,
with distinct outside vertices, so the four edges form a cycle.
-/

set_option autoImplicit false

namespace Q9SparseCocycleSupport

open Finset

private abbrev Face := Finset (Fin 6)

private def edges : Finset Face := (univ : Face).powersetCard 2
private def triples : Finset Face := (univ : Face).powersetCard 3

private def edgeCount (E : Finset Face) (t : Face) : ℕ := (E.filter (· ⊆ t)).card

/-- The unordered triples containing exactly one edge of `E`. -/
def singleEdgeTriples (E : Finset (Finset (Fin 6))) : Finset (Finset (Fin 6)) :=
  triples.filter fun t => edgeCount E t = 1

-- Test containment first so the edge count is evaluated only on triples through `e`.
private def singleEdgeTriplesThrough (E : Finset Face) (e : Face) : Finset Face :=
  triples.filter fun t => e ⊆ t ∧ edgeCount E t = 1

private abbrev IsFourCycle (E : Finset Face) : Prop :=
  ∃ a b c d : Fin 6,
    ({a, b, c, d} : Face).card = 4 ∧ E = {{a, b}, {b, c}, {c, d}, {d, a}}

set_option maxRecDepth 32768 in
set_option maxHeartbeats 60000000 in
private theorem check_sparse_support :
    ∀ k ∈ Icc (1 : ℕ) 4, ∀ E ∈ edges.powersetCard k,
      (∀ v : Fin 6, (E.filter (v ∈ ·)).card ≤ 3) →
      (∀ e ∈ E, (singleEdgeTriplesThrough E e).card ≤ 2) →
      ((k = 3 ∧ (∃ c : Fin 6, ∀ e ∈ E, c ∈ e) ∧ (singleEdgeTriples E).card = 6) ∨
        (k = 4 ∧ IsFourCycle E ∧ (singleEdgeTriples E).card = 8)) ∧
      (∀ e ∈ E, (singleEdgeTriplesThrough E e).card = 2) := by
  decide +kernel

/-- The forced triples exhaust the support, with edge and triple counts `(3, 6)`
or `(4, 8)`. Their total cardinality is `9` or `12`. The equality also forces
every member of `B` to have cardinality three. -/
theorem sparse_cocycle_support (E B : Finset (Finset (Fin 6)))
    (hedge : ∀ e ∈ E, e.card = 2) (hmin : 1 ≤ E.card) (hmax : E.card ≤ 4)
    (hdegree : ∀ v : Fin 6, (E.filter (v ∈ ·)).card ≤ 3)
    (hforced : singleEdgeTriples E ⊆ B)
    (hsupported : ∀ t ∈ B, ∃ e ∈ E, e ⊆ t)
    (hcap : ∀ e ∈ E, (B.filter (e ⊆ ·)).card ≤ 2) :
    B = singleEdgeTriples E ∧
      ((E.card = 3 ∧ B.card = 6) ∨ (E.card = 4 ∧ B.card = 8)) := by
  have hthrough (e : Face) : singleEdgeTriplesThrough E e ⊆ B.filter (e ⊆ ·) := by
    intro t ht
    obtain ⟨ht3, het, hone⟩ := mem_filter.mp ht
    exact mem_filter.mpr ⟨hforced (mem_filter.mpr ⟨ht3, hone⟩), het⟩
  have hE : E ∈ edges.powersetCard E.card :=
    mem_powersetCard.mpr
      ⟨fun e he => mem_powersetCard.mpr ⟨subset_univ e, hedge e he⟩, rfl⟩
  obtain ⟨hcases, htight⟩ :=
    check_sparse_support E.card (mem_Icc.mpr ⟨hmin, hmax⟩) E hE hdegree
      (fun e he => (card_le_card (hthrough e)).trans (hcap e he))
  have hB : B = singleEdgeTriples E := by
    refine Subset.antisymm ?_ hforced
    intro t ht
    obtain ⟨e, he, het⟩ := hsupported t ht
    have hfiber : singleEdgeTriplesThrough E e = B.filter (e ⊆ ·) :=
      eq_of_subset_of_card_le (hthrough e) ((hcap e he).trans (htight e he).ge)
    have ht' : t ∈ singleEdgeTriplesThrough E e := by
      rw [hfiber]
      exact mem_filter.mpr ⟨ht, het⟩
    obtain ⟨ht3, _, hone⟩ := mem_filter.mp ht'
    exact mem_filter.mpr ⟨ht3, hone⟩
  refine ⟨hB, ?_⟩
  rw [hB]
  rcases hcases with ⟨hcard, _, hsingles⟩ | ⟨hcard, _, hsingles⟩
  · exact Or.inl ⟨hcard, hsingles⟩
  · exact Or.inr ⟨hcard, hsingles⟩

end Q9SparseCocycleSupport
