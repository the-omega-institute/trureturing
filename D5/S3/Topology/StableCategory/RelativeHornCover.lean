/- GID: D5/S3/Topology/StableCategory/RelativeHornCover
   generality: G
   mirror-B: D5/B/S3/Topology/StableCategory/RelativeHornCover
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The first subdivision of a simplex horn attachment requires one piece per facet. -/

import D5.S3.Topology.StableCategory.RelativeCoverNecessity
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Data.Fin.Pigeonhole
import Mathlib.Data.Fintype.Option
import Mathlib.Order.Interval.Finset.Fin

/-!
# First-subdivision relative covers of a simplex horn

A local benchmark for Question 6.3 of Mosquera–Lois and Tanaka
(https://arxiv.org/html/2609.39615v1#S6.Thmtheorem3).

A region with a fence fixing its old trace can contain at most one adjoined
chain from a pairwise disjoint family of maximal strict lower chains.
For the cone poset over a simplex horn, cyclic arcs yield such a family of
size equal to the dimension. The horn facets give a cover of that size.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Topology.StableCategory.RelativeHornCover

open PartialOrder (NonemptyFiniteChains)
open MaximalChainCoverExtension (chainsAvoiding)
open RelativeCoverNecessity
open scoped Classical

/-- A finite lower cover with relative fences fixing each piece's old trace. -/
def IsRelativeLowerCover {P : Type*} [PartialOrder P] (T : Set P) {k : ℕ}
    (A E : Fin k → Set (NonemptyFiniteChains P)) : Prop :=
  (∀ i, IsLowerSet (A i)) ∧
  (∀ s, ∃ i, s ∈ A i) ∧
  (∀ i, A i ∩ chainsAvoiding T = E i) ∧
  (∀ i, RelativeOrderFence (A i) (E i))

/-- A piece containing the join of one of the disjoint chains cannot contain
the join of another. In fact, only coverage of these joins is needed. -/
theorem card_le_of_disjoint_maximal_strict_lower_chains
    {P : Type*} [PartialOrder P] {T : Set P} (hT : ∀ x ∈ T, IsMax x)
    {t : P} (ht : t ∈ T) {n k : ℕ} (M : Fin n → NonemptyFiniteChains P)
    (hM : ∀ j, Maximal (StrictLowerChain t) (M j))
    (hdisj : Pairwise (fun i j => Disjoint (M i).finset (M j).finset))
    {A E : Fin k → Set (NonemptyFiniteChains P)}
    (hA : ∀ i, IsLowerSet (A i))
    (hcover : ∀ j, ∃ i, adjoinTop t (M j) (hM j).1 ∈ A i)
    (htrace : ∀ i, A i ∩ chainsAvoiding T = E i)
    (hfence : ∀ i, RelativeOrderFence (A i) (E i)) : n ≤ k := by
  choose piece hpiece using hcover
  apply Fin.le_of_injective piece
  intro i j hij
  by_contra hne
  have hj : adjoinTop t (M j) (hM j).1 ∈ A (piece i) := by
    rw [hij]
    exact hpiece j
  obtain ⟨c, _, hc⟩ := exists_common_strict_predecessor_of_relative_fence hT
    (hA (piece i)) (htrace (piece i)) ht ⟨M i, hM i, hpiece i⟩ (hfence (piece i))
  exact (Finset.disjoint_left.mp (hdisj hne)) (hc (M i) (hM i) (hpiece i))
    (hc (M j) (hM j) hj)

/-- Nonempty retained faces of the `d`-simplex horn. The distinguished
vertex is `none`. The condition on the other vertices excludes the simplex
and the facet opposite the distinguished vertex. -/
abbrev HornFace (d : ℕ) :=
  {F : Finset (Option (Fin d)) // F.Nonempty ∧ ∃ i : Fin d, some i ∉ F}

/-- The horn face poset with a greatest element adjoined. -/
abbrev HornWithTop (d : ℕ) := WithTop (HornFace d)

private def facet {d : ℕ} (i : Fin d) : HornFace d :=
  ⟨Finset.univ.erase (some i), ⟨none, Finset.mem_erase.mpr ⟨by simp, Finset.mem_univ _⟩⟩,
    ⟨i, Finset.notMem_erase _ _⟩⟩

private theorem le_facet {d : ℕ} {F : HornFace d} {i : Fin d}
    (hi : some i ∉ F.val) : F ≤ facet i :=
  fun _ hx => Finset.mem_erase.mpr ⟨fun he => hi (he ▸ hx), Finset.mem_univ _⟩

private theorem facet_card {d : ℕ} (i : Fin d) : (facet i).val.card = d := by
  change (Finset.univ.erase (some i)).card = d
  rw [Finset.card_erase_of_mem (Finset.mem_univ _)]
  simp [Fintype.card_option]

private theorem hornFace_card_le {d : ℕ} (F : HornFace d) : F.val.card ≤ d := by
  obtain ⟨i, hi⟩ := F.property.2
  exact (Finset.card_le_card (le_facet hi)).trans_eq (facet_card i)

private theorem facet_injective {d : ℕ} : Function.Injective (@facet d) := by
  intro i j hij
  by_contra hne
  have hi : some i ∈ (facet j).val :=
    Finset.mem_erase.mpr ⟨fun h => hne (Option.some.inj h), Finset.mem_univ _⟩
  exact (Finset.notMem_erase (some i) Finset.univ)
    (show some i ∈ (facet i).val from hij ▸ hi)

section CyclicChains

variable {m : ℕ}

private def ordinaryVertex (i : Fin (m + 2)) : Fin (m + 2) ↪ Option (Fin (m + 2)) :=
  ⟨fun j => some (j + i), fun _ _ h => add_right_cancel (Option.some.inj h)⟩

private def arcVertices (i r : Fin (m + 2)) : Finset (Option (Fin (m + 2))) :=
  (Finset.Iio r).map (ordinaryVertex i)

private theorem mem_arcVertices {i r x : Fin (m + 2)} :
    some x ∈ arcVertices i r ↔ x - i < r := by
  constructor
  · intro hx
    obtain ⟨j, hj, heq⟩ := Finset.mem_map.mp hx
    change some (j + i) = some x at heq
    have hji : j = x - i := by rw [← Option.some.inj heq, add_sub_cancel_right]
    exact hji ▸ Finset.mem_Iio.mp hj
  · intro hx
    refine Finset.mem_map.mpr ⟨x - i, Finset.mem_Iio.mpr hx, ?_⟩
    change some (x - i + i) = some x
    rw [sub_add_cancel]

private theorem predecessor_notMem_arc (i r : Fin (m + 2)) :
    some (i - 1) ∉ arcVertices i r := by
  rw [mem_arcVertices, sub_right_comm i 1 i, sub_self]
  have hlast : (0 : Fin (m + 2)) - 1 = Fin.last (m + 1) := by
    apply Fin.ext
    simp
  rw [hlast]
  exact (Fin.le_last r).not_gt

/-- The start is the unique ordinary vertex in a nonempty proper cyclic
arc whose predecessor lies outside the arc. -/
private theorem eq_start_of_mem_of_pred_notMem {i r x : Fin (m + 2)}
    (hx : some x ∈ arcVertices i r) (hp : some (x - 1) ∉ arcVertices i r) : x = i := by
  have hprev : ¬ x - i - 1 < r := by
    rw [sub_right_comm x i 1]
    exact fun h => hp (mem_arcVertices.mpr h)
  have hlt : x - i < x - i - 1 :=
    (mem_arcVertices.mp hx).trans_le (le_of_not_gt hprev)
  exact sub_eq_zero.mp (Fin.lt_sub_one_iff.mp hlt)

private theorem start_mem_arc (i r : Fin (m + 2)) (hr : r ≠ 0) :
    some i ∈ arcVertices i r := by
  rw [mem_arcVertices, sub_self]
  exact lt_of_le_of_ne (Fin.zero_le r) hr.symm

private def arcFace (i r : Fin (m + 2)) (hr : r ≠ 0) : HornFace (m + 2) :=
  ⟨arcVertices i r, ⟨some i, start_mem_arc i r hr⟩, ⟨i - 1, predecessor_notMem_arc i r⟩⟩

/-- Index zero denotes the top face in the chain. Other indices are the
lengths of the arcs starting at `i`. The final step adds `none`. -/
private def cyclicFace (i r : Fin (m + 2)) : HornFace (m + 2) :=
  if hr : r = 0 then facet (i - 1) else arcFace i r hr

private theorem cyclicFace_card (i r : Fin (m + 2)) :
    (cyclicFace i r).val.card = if r = 0 then m + 2 else r.val := by
  by_cases hr : r = 0
  · simp [cyclicFace, hr, facet_card]
  · simp [cyclicFace, hr, arcFace, arcVertices, Fin.card_Iio]

private theorem cyclicFace_comparable (i r s : Fin (m + 2)) :
    cyclicFace i r ≤ cyclicFace i s ∨ cyclicFace i s ≤ cyclicFace i r := by
  by_cases hr : r = 0
  · by_cases hs : s = 0
    · exact Or.inl (by simp [cyclicFace, hr, hs])
    · simpa only [cyclicFace, dite_eq_left hr, dite_eq_right hs] using
        (Or.inr (le_facet (F := arcFace i s hs) (predecessor_notMem_arc i s)) :
          facet (i - 1) ≤ arcFace i s hs ∨ arcFace i s hs ≤ facet (i - 1))
  · by_cases hs : s = 0
    · simpa only [cyclicFace, dite_eq_right hr, dite_eq_left hs] using
        (Or.inl (le_facet (F := arcFace i r hr) (predecessor_notMem_arc i r)) :
          arcFace i r hr ≤ facet (i - 1) ∨ facet (i - 1) ≤ arcFace i r hr)
    · have hmono {a b : Fin (m + 2)} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≤ b) :
          arcFace i a ha ≤ arcFace i b hb :=
        Finset.map_subset_map.mpr (fun _ hx =>
          Finset.mem_Iio.mpr ((Finset.mem_Iio.mp hx).trans_le hab))
      simpa only [cyclicFace, dite_eq_right hr, dite_eq_right hs] using
        (le_total r s).elim (fun h => Or.inl (hmono hr hs h)) (fun h => Or.inr (hmono hs hr h))

private def cyclicChain (i : Fin (m + 2)) : NonemptyFiniteChains (HornWithTop (m + 2)) where
  finset := Finset.univ.image (fun r => (cyclicFace i r : HornWithTop (m + 2)))
  nonempty := ⟨(cyclicFace i 0 : HornWithTop (m + 2)),
    Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩
  comparable := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hy
    exact (cyclicFace_comparable i r s).imp WithTop.coe_le_coe.mpr WithTop.coe_le_coe.mpr

private theorem cyclicFace_mem_chain (i r : Fin (m + 2)) :
    (cyclicFace i r : HornWithTop (m + 2)) ∈ (cyclicChain i).finset :=
  Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩

private theorem exists_cyclicFace_card (i : Fin (m + 2)) (F : HornFace (m + 2)) :
    ∃ r, (cyclicFace i r).val.card = F.val.card := by
  obtain hlt | heq := lt_or_eq_of_le (hornFace_card_le F)
  · let r : Fin (m + 2) := ⟨F.val.card, hlt⟩
    have hne : r ≠ 0 := fun h => F.property.1.card_ne_zero (congrArg Fin.val h)
    exact ⟨r, by simp only [cyclicFace_card, ite_eq_right hne, r]⟩
  · exact ⟨0, by simp [cyclicFace_card, heq]⟩

private theorem cyclicChain_maximal (i : Fin (m + 2)) :
    Maximal (StrictLowerChain (⊤ : HornWithTop (m + 2))) (cyclicChain i) := by
  constructor
  · intro x hx
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hx
    exact WithTop.coe_lt_top _
  · intro S hS hsub x hx
    obtain ⟨F, rfl⟩ := WithTop.ne_top_iff_exists.mp (hS x hx).ne
    obtain ⟨r, hr⟩ := exists_cyclicFace_card i F
    have hy := cyclicFace_mem_chain i r
    have hcomp : (F : HornWithTop (m + 2)) ≤ ↑(cyclicFace i r) ∨
        (cyclicFace i r : HornWithTop (m + 2)) ≤ ↑F :=
      S.comparable ⟨_, hx⟩ ⟨_, hsub hy⟩
    have heq : F = cyclicFace i r := by
      apply Subtype.ext
      rcases hcomp with hle | hge
      · have hsub : F ≤ cyclicFace i r := WithTop.coe_le_coe.mp hle
        exact Finset.eq_of_subset_of_card_le hsub hr.le
      · have hsub : cyclicFace i r ≤ F := WithTop.coe_le_coe.mp hge
        exact (Finset.eq_of_subset_of_card_le hsub hr.ge).symm
    exact heq.symm ▸ hy

private theorem cyclicFace_start_injective {i j r : Fin (m + 2)}
    (h : cyclicFace i r = cyclicFace j r) : i = j := by
  by_cases hr : r = 0
  · have hfacet : facet (i - 1) = facet (j - 1) := by simpa [cyclicFace, hr] using h
    exact sub_left_injective (facet_injective hfacet)
  · have harc : arcVertices i r = arcVertices j r :=
      congrArg Subtype.val (by simpa only [cyclicFace, dite_eq_right hr] using h :
        arcFace i r hr = arcFace j r hr)
    exact eq_start_of_mem_of_pred_notMem
      (harc ▸ start_mem_arc i r hr) (harc ▸ predecessor_notMem_arc i r)

private theorem cyclicChain_disjoint :
    Pairwise (fun i j : Fin (m + 2) => Disjoint (cyclicChain i).finset (cyclicChain j).finset) := by
  intro i j hij
  refine Finset.disjoint_left.mpr (fun x hx hy => hij ?_)
  obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨s, _, heq⟩ := Finset.mem_image.mp hy
  have hfaces : cyclicFace j s = cyclicFace i r := WithTop.coe_inj.mp heq
  have hcards := congrArg (fun F : HornFace (m + 2) => F.val.card) hfaces
  rw [cyclicFace_card, cyclicFace_card] at hcards
  have hsr : s = r := by
    by_cases hs : s = 0 <;> by_cases hr : r = 0
    · exact hs.trans hr.symm
    · simp only [ite_eq_left hs, ite_eq_right hr] at hcards
      exact (r.isLt.ne hcards.symm).elim
    · simp only [ite_eq_right hs, ite_eq_left hr] at hcards
      exact (s.isLt.ne hcards).elim
    · exact Fin.ext (by simpa only [ite_eq_right hs, ite_eq_right hr] using hcards)
  subst s
  exact (cyclicFace_start_injective hfaces).symm

end CyclicChains

/-- For every simplex dimension at least two, the cyclic chains of the
retained horn faces are pairwise disjoint and maximal below the new top. -/
theorem exists_horn_cyclic_maximal_chains {d : ℕ} (hd : 2 ≤ d) :
    ∃ M : Fin d → NonemptyFiniteChains (HornWithTop d),
      (∀ i, Maximal (StrictLowerChain (⊤ : HornWithTop d)) (M i)) ∧
      Pairwise (fun i j => Disjoint (M i).finset (M j).finset) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, d = m + 2 := ⟨d - 2, by omega⟩
  exact ⟨cyclicChain, cyclicChain_maximal, cyclicChain_disjoint⟩

/-- The first chain subdivision of the horn with a new top needs at least
`d` pieces, even when different pieces have different old traces. -/
theorem horn_le_of_relative_lower_cover {d k : ℕ} (hd : 2 ≤ d)
    {A E : Fin k → Set (NonemptyFiniteChains (HornWithTop d))}
    (hcover : IsRelativeLowerCover ({⊤} : Set (HornWithTop d)) A E) : d ≤ k := by
  obtain ⟨M, hM, hdisj⟩ := exists_horn_cyclic_maximal_chains hd
  obtain ⟨hA, hcover, htrace, hfence⟩ := hcover
  exact card_le_of_disjoint_maximal_strict_lower_chains
    (fun x hx => (Set.mem_singleton_iff.mp hx).symm ▸ isMax_top)
    (Set.mem_singleton _) M hM hdisj hA
    (fun j => hcover (adjoinTop ⊤ (M j) (hM j).1)) htrace hfence

section UpperBound

variable {P : Type*} [PartialOrder P] [OrderTop P]

private def facetRegion (c : P) : Set (NonemptyFiniteChains P) :=
  {s | (⊤ : P) ∈ s.finset → ∀ x ∈ s.finset, x ≠ ⊤ → x ≤ c}

private theorem mem_old_iff {s : NonemptyFiniteChains P} :
    s ∈ chainsAvoiding ({⊤} : Set P) ↔ (⊤ : P) ∉ s.finset := by
  constructor
  · intro hs ht
    exact hs ⊤ ht (Set.mem_singleton _)
  · intro hs x hx hxt
    exact hs (Set.mem_singleton_iff.mp hxt ▸ hx)

private def insertFacet (c : P) (s : facetRegion c) : NonemptyFiniteChains P :=
  if ht : (⊤ : P) ∈ s.val.finset then
    ⟨insert c s.val.finset, s.val.nonempty.mono (Finset.subset_insert _ _), by
      have hcomp {x : P} (hx : x ∈ s.val.finset) : x ≤ c ∨ c ≤ x := by
        by_cases hxt : x = ⊤
        · subst x
          exact Or.inr le_top
        · exact Or.inl (s.property ht x hx hxt)
      rintro ⟨x, hx⟩ ⟨y, hy⟩
      change x ≤ y ∨ y ≤ x
      rcases Finset.mem_insert.mp hx with rfl | hx
      · rcases Finset.mem_insert.mp hy with rfl | hy
        · exact Or.inl le_rfl
        · exact (hcomp hy).symm
      · rcases Finset.mem_insert.mp hy with rfl | hy
        · exact hcomp hx
        · exact s.val.comparable ⟨x, hx⟩ ⟨y, hy⟩⟩
  else s.val

private theorem mem_insertFacet {c x : P} {s : facetRegion c} :
    x ∈ (insertFacet c s).finset ↔
      x ∈ s.val.finset ∨ ((⊤ : P) ∈ s.val.finset ∧ x = c) := by
  by_cases ht : (⊤ : P) ∈ s.val.finset
  · simp [insertFacet, ht, or_comm]
  · simp [insertFacet, ht]

private def eraseTopAfterInsert (c : P) (hc : c ≠ ⊤) (s : facetRegion c) :
    NonemptyFiniteChains P := by
  refine ⟨(insertFacet c s).finset.erase ⊤, ?_, ?_⟩
  · by_cases ht : (⊤ : P) ∈ s.val.finset
    · exact ⟨c, Finset.mem_erase.mpr ⟨hc, mem_insertFacet.mpr (Or.inr ⟨ht, rfl⟩)⟩⟩
    · obtain ⟨x, hx⟩ := s.val.nonempty
      exact ⟨x, Finset.mem_erase.mpr ⟨fun h => ht (h ▸ hx), mem_insertFacet.mpr (Or.inl hx)⟩⟩
  · rintro ⟨x, hx⟩ ⟨y, hy⟩
    exact (insertFacet c s).comparable ⟨x, (Finset.mem_erase.mp hx).2⟩
      ⟨y, (Finset.mem_erase.mp hy).2⟩

private theorem facetRegion_fence {c : P} (hc : c ≠ ⊤) :
    RelativeOrderFence (facetRegion c) (chainsAvoiding ({⊤} : Set P)) := by
  have hmono : Monotone (insertFacet c) := by
    intro s t hst x hx
    change s.val.finset ⊆ t.val.finset at hst
    exact mem_insertFacet.mpr
      ((mem_insertFacet.mp hx).imp (fun h => hst h) (fun h => ⟨hst h.1, h.2⟩))
  let up : FixedOrderMaps (facetRegion c) (chainsAvoiding ({⊤} : Set P)) :=
    ⟨⟨insertFacet c, hmono⟩, fun s hs => by
      change insertFacet c s = s.val
      simp only [insertFacet, dite_eq_right (mem_old_iff.mp hs)]⟩
  let down : FixedOrderMaps (facetRegion c) (chainsAvoiding ({⊤} : Set P)) :=
    ⟨⟨eraseTopAfterInsert c hc, fun _ _ h => Finset.erase_subset_erase _ (hmono h)⟩,
      fun s hs => by
        have ht := mem_old_iff.mp hs
        apply NonemptyFiniteChains.ext
        change (insertFacet c s).finset.erase ⊤ = s.val.finset
        simp only [insertFacet, dite_eq_right ht, Finset.erase_eq_of_notMem ht]⟩
  have hup : (FixedOrderMaps.inclusion (facetRegion c) (chainsAvoiding ({⊤} : Set P))).val ≤
      up.val :=
    OrderHom.le_def.mpr (fun _ _ hx => mem_insertFacet.mpr (Or.inl hx))
  have hdown : down.val ≤ up.val :=
    OrderHom.le_def.mpr (fun _ => Finset.erase_subset _ _)
  exact ⟨down, .trans _ _ _ (.rel _ _ hup) (.symm _ _ (.rel _ _ hdown)), fun s =>
    mem_old_iff.mpr (Finset.notMem_erase _ _)⟩

/-- A nonempty family of proper elements cofinal below the top gives a
cover by regions, each with the entire old region as its trace. -/
private theorem relative_lower_cover_of_cofinal {k : ℕ} (i₀ : Fin k)
    (c : Fin k → P) (hc : ∀ i, c i ≠ ⊤) (hcofinal : ∀ x : P, x ≠ ⊤ → ∃ i, x ≤ c i) :
    IsRelativeLowerCover ({⊤} : Set P) (fun i => facetRegion (c i))
      (fun _ => chainsAvoiding ({⊤} : Set P)) := by
  refine ⟨?_, ?_, ?_, fun i => facetRegion_fence (hc i)⟩
  · intro i s t hst ht hsTop x hx hne
    exact ht (hst hsTop) x (hst hx) hne
  · intro s
    by_cases hs : (s.finset.erase (⊤ : P)).Nonempty
    · obtain ⟨a, ha⟩ := Finset.exists_maximal hs
      obtain ⟨hne, haS⟩ := Finset.mem_erase.mp ha.1
      obtain ⟨i, hi⟩ := hcofinal a hne
      refine ⟨i, fun _ x hx hxt => ?_⟩
      have hxa : x ≤ a :=
        (s.comparable ⟨x, hx⟩ ⟨a, haS⟩).elim id
          (fun h => ha.2 (Finset.mem_erase.mpr ⟨hxt, hx⟩) h)
      exact hxa.trans hi
    · exact ⟨i₀, fun _ x hx hxt => (hs ⟨x, Finset.mem_erase.mpr ⟨hxt, hx⟩⟩).elim⟩
  · intro i
    ext s
    exact ⟨fun hs => hs.2, fun hs => ⟨fun ht => (mem_old_iff.mp hs ht).elim, hs⟩⟩

end UpperBound

/-- At the first subdivision of the horn face poset with an adjoined top,
the least number of relative lower pieces with the full old trace is `d`.
A piece is allowed to move through the ambient chain poset, with every row
of its fence fixing the common old region. -/
theorem isLeast_horn_relative_lower_cover {d : ℕ} (hd : 2 ≤ d) :
    IsLeast {k : ℕ | ∃ A : Fin k → Set (NonemptyFiniteChains (HornWithTop d)),
      IsRelativeLowerCover ({⊤} : Set (HornWithTop d)) A
        (fun _ => chainsAvoiding ({⊤} : Set (HornWithTop d)))} d := by
  refine ⟨?_, ?_⟩
  · let c (i : Fin d) : HornWithTop d := facet i
    refine ⟨fun i => facetRegion (c i), relative_lower_cover_of_cofinal
      ⟨0, by omega⟩ c (fun i => WithTop.coe_ne_top) ?_⟩
    intro x hx
    obtain ⟨F, rfl⟩ := WithTop.ne_top_iff_exists.mp hx
    obtain ⟨i, hi⟩ := F.property.2
    exact ⟨i, WithTop.coe_le_coe.mpr (le_facet hi)⟩
  · intro k hk
    obtain ⟨A, hA⟩ := hk
    exact horn_le_of_relative_lower_cover hd hA

end D5.S3.Topology.StableCategory.RelativeHornCover
