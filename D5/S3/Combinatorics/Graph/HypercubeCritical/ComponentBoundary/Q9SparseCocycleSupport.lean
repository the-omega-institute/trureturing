/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SparseCocycleSupport
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SparseCocycleSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Finset.Powerset]
   utility: none
   digest: Sparse pivot graphs force triple support of order nine or twelve. -/

import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
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

private theorem filter_singleEdgeTriples (E : Finset Face) (e : Face) :
    (singleEdgeTriples E).filter (e ⊆ ·) = singleEdgeTriplesThrough E e := by
  ext t
  simp only [singleEdgeTriples, singleEdgeTriplesThrough, mem_filter]
  exact ⟨fun ⟨⟨ht, hone⟩, he⟩ => ⟨ht, he, hone⟩,
    fun ⟨ht, he, hone⟩ => ⟨⟨ht, hone⟩, he⟩⟩

private theorem singleEdgeTriples_iff_of_isolates (E : Finset Face) (S : Face)
    (hedge : ∀ e ∈ E, e.card = 2) (hsub : ∀ e ∈ E, e ⊆ S) (hisolates : (Sᶜ).card = 2)
    (htight : ∀ e ∈ E, (singleEdgeTriplesThrough E e).card = 2) (t : Face) :
    t ∈ singleEdgeTriples E ↔ ∃ e ∈ E, ∃ v ∉ S, t = insert v e := by
  have hnot (e : Face) (he : e ∈ E) {v : Fin 6} (hv : v ∈ Sᶜ) : v ∉ e :=
    fun h => (mem_compl.mp hv) (hsub e he h)
  have hfiber (e : Face) (he : e ∈ E) :
      (Sᶜ).image (fun v => insert v e) = singleEdgeTriplesThrough E e := by
    apply eq_of_subset_of_card_le
    · intro u hu
      obtain ⟨v, hv, rfl⟩ := mem_image.mp hu
      have hcard : (insert v e).card = 3 := by
        rw [card_insert_of_notMem (hnot e he hv), hedge e he]
      have hunique : E.filter (· ⊆ insert v e) = {e} := by
        refine eq_singleton_iff_unique_mem.mpr ⟨mem_filter.mpr ⟨he, subset_insert v e⟩, ?_⟩
        intro f hf
        obtain ⟨hfE, hfSub⟩ := mem_filter.mp hf
        exact eq_of_subset_of_card_le ((subset_insert_iff_of_notMem (hnot f hfE hv)).mp hfSub)
          (by rw [hedge e he, hedge f hfE])
      exact mem_filter.mpr
        ⟨mem_powersetCard.mpr ⟨subset_univ _, hcard⟩, subset_insert v e, by
          change (E.filter (· ⊆ insert v e)).card = 1
          rw [hunique, card_singleton]⟩
    · have hinj : Set.InjOn (fun v : Fin 6 => insert v e) (↑(Sᶜ) : Set (Fin 6)) :=
        fun _ hv _ _ h => (insert_inj (hnot e he (mem_coe.mp hv))).mp h
      exact (htight e he).le.trans ((card_image_of_injOn hinj).trans hisolates).ge
  constructor
  · intro ht
    have hone : (E.filter (· ⊆ t)).card = 1 := by
      change t ∈ triples.filter (fun u => edgeCount E u = 1) at ht
      exact (mem_filter.mp ht).2
    have hpositive : 0 < (E.filter (· ⊆ t)).card := by
      simpa only [hone] using Nat.zero_lt_succ 0
    obtain ⟨e, he⟩ := card_pos.mp hpositive
    obtain ⟨heE, het⟩ := mem_filter.mp he
    have ht' : t ∈ (singleEdgeTriples E).filter (e ⊆ ·) := mem_filter.mpr ⟨ht, het⟩
    rw [filter_singleEdgeTriples, ← hfiber e heE] at ht'
    obtain ⟨v, hv, hvt⟩ := mem_image.mp ht'
    exact ⟨e, heE, v, mem_compl.mp hv, hvt.symm⟩
  · rintro ⟨e, he, v, hv, rfl⟩
    have ht' : insert v e ∈ (singleEdgeTriples E).filter (e ⊆ ·) := by
      rw [filter_singleEdgeTriples, ← hfiber e he]
      exact mem_image.mpr ⟨v, mem_compl.mpr hv, rfl⟩
    exact (mem_filter.mp ht').1

/-- A nonempty graph on six vertices with at most four edges and the indicated
degree and triple bounds is a three-edge star or a four-cycle. In the cycle
case the singleton-edge triples are exactly the cycle edges extended by one
of the two isolated vertices. Every edge attains the triple bound. -/
theorem sparse_pivot_graph_classification (E : Finset (Finset (Fin 6)))
    (hedge : ∀ e ∈ E, e.card = 2) (hmin : 1 ≤ E.card) (hmax : E.card ≤ 4)
    (hdegree : ∀ v : Fin 6, (E.filter (v ∈ ·)).card ≤ 3)
    (hcap : ∀ e ∈ E, ((singleEdgeTriples E).filter (e ⊆ ·)).card ≤ 2) :
    ((E.card = 3 ∧ (∃ c : Fin 6, ∀ e ∈ E, c ∈ e) ∧ (singleEdgeTriples E).card = 6) ∨
      (E.card = 4 ∧ (singleEdgeTriples E).card = 8 ∧
        ∃ a b c d : Fin 6, ({a, b, c, d} : Finset (Fin 6)).card = 4 ∧
          E = {{a, b}, {b, c}, {c, d}, {d, a}} ∧
          ∀ t : Finset (Fin 6), t ∈ singleEdgeTriples E ↔
            ∃ e ∈ E, ∃ v ∉ ({a, b, c, d} : Finset (Fin 6)), t = insert v e)) ∧
    (∀ e ∈ E, ((singleEdgeTriples E).filter (e ⊆ ·)).card = 2) := by
  have hE : E ∈ edges.powersetCard E.card :=
    mem_powersetCard.mpr
      ⟨fun e he => mem_powersetCard.mpr ⟨subset_univ e, hedge e he⟩, rfl⟩
  obtain ⟨hcases, htight⟩ :=
    check_sparse_support E.card (mem_Icc.mpr ⟨hmin, hmax⟩) E hE hdegree
      (fun e he => by simpa only [filter_singleEdgeTriples] using hcap e he)
  refine ⟨?_, fun e he => by simpa only [filter_singleEdgeTriples] using htight e he⟩
  rcases hcases with hstar | ⟨hcard, ⟨a, b, c, d, hvertices, hcycle⟩, hsingles⟩
  · exact Or.inl hstar
  · have hsub (e : Face) (he : e ∈ E) : e ⊆ ({a, b, c, d} : Face) := by
      rw [hcycle] at he
      simp only [mem_insert, mem_singleton] at he
      rcases he with rfl | rfl | rfl | rfl <;> simp [insert_subset_iff, singleton_subset_iff]
    have hisolates : (({a, b, c, d} : Face)ᶜ).card = 2 := by
      rw [card_compl, Fintype.card_fin, hvertices]
    exact Or.inr ⟨hcard, hsingles, a, b, c, d, hvertices, hcycle,
      singleEdgeTriples_iff_of_isolates E {a, b, c, d} hedge hsub hisolates htight⟩

/-- Singleton-edge triples exhaust every admissible family. The star has six
such triples and the four-cycle has eight, with the explicit description below. -/
theorem sparse_cocycle_support_classification (E B : Finset (Finset (Fin 6)))
    (hedge : ∀ e ∈ E, e.card = 2) (hmin : 1 ≤ E.card) (hmax : E.card ≤ 4)
    (hdegree : ∀ v : Fin 6, (E.filter (v ∈ ·)).card ≤ 3)
    (hforced : singleEdgeTriples E ⊆ B)
    (hsupported : ∀ t ∈ B, ∃ e ∈ E, e ⊆ t)
    (hcap : ∀ e ∈ E, (B.filter (e ⊆ ·)).card ≤ 2) :
    B = singleEdgeTriples E ∧
      ((E.card = 3 ∧ (∃ c : Fin 6, ∀ e ∈ E, c ∈ e) ∧ B.card = 6) ∨
        (E.card = 4 ∧ B.card = 8 ∧
          ∃ a b c d : Fin 6, ({a, b, c, d} : Finset (Fin 6)).card = 4 ∧
            E = {{a, b}, {b, c}, {c, d}, {d, a}} ∧
            ∀ t : Finset (Fin 6), t ∈ B ↔
              ∃ e ∈ E, ∃ v ∉ ({a, b, c, d} : Finset (Fin 6)), t = insert v e)) := by
  have hthrough (e : Face) : (singleEdgeTriples E).filter (e ⊆ ·) ⊆ B.filter (e ⊆ ·) := by
    intro t ht
    obtain ⟨htSingle, het⟩ := mem_filter.mp ht
    exact mem_filter.mpr ⟨hforced htSingle, het⟩
  obtain ⟨hcases, htight⟩ := sparse_pivot_graph_classification E hedge hmin hmax hdegree
    (fun e he => (card_le_card (hthrough e)).trans (hcap e he))
  have hB : B = singleEdgeTriples E := by
    refine Subset.antisymm ?_ hforced
    intro t ht
    obtain ⟨e, he, het⟩ := hsupported t ht
    have hfiber : (singleEdgeTriples E).filter (e ⊆ ·) = B.filter (e ⊆ ·) :=
      eq_of_subset_of_card_le (hthrough e) ((hcap e he).trans (htight e he).ge)
    have ht' : t ∈ (singleEdgeTriples E).filter (e ⊆ ·) := by
      rw [hfiber]
      exact mem_filter.mpr ⟨ht, het⟩
    exact (mem_filter.mp ht').1
  refine ⟨hB, ?_⟩
  rw [hB]
  exact hcases

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
  obtain ⟨hB, hcases⟩ :=
    sparse_cocycle_support_classification E B hedge hmin hmax hdegree hforced hsupported hcap
  refine ⟨hB, ?_⟩
  rcases hcases with ⟨hcard, _, hsingles⟩ | ⟨hcard, hsingles, _⟩
  · exact Or.inl ⟨hcard, hsingles⟩
  · exact Or.inr ⟨hcard, hsingles⟩

end Q9SparseCocycleSupport
