/- GID: D5/S3/Combinatorics/Graph/DUFComponents
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/DUFComponents
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S3/Combinatorics/Graph/DUFCounting]
   utility: none
   digest: Reciprocal four-star fibers form saturated complete bipartite components of vertex links. -/

import D5.S3.Combinatorics.Graph.DUFCounting
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.DUFComponents

open Finset DUFStructure DUFCounting
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A vertex link uses the actual triples of H. -/
def link (H : Finset (Finset V)) (c : V) : SimpleGraph V where
  Adj x y := x ≠ y ∧ c ∉ ({x, y} : Finset V) ∧ ({c, x, y} : Finset V) ∈ H
  symm := ⟨by intro x y h; simpa [pair_comm, ne_comm] using h⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

/-- A complete bipartite configuration, specified by its actual triples. -/
def CompleteBlock (H : Finset (Finset V)) (c : V) (A S : Finset V) : Prop :=
  A.card = 4 ∧ S.card = 4 ∧ c ∉ A ∧ c ∉ S ∧ Disjoint A S ∧
    ∀ x ∈ A, ∀ y ∈ S, ({c, x, y} : Finset V) ∈ H

/-- Center and support are the identity of a block; the bipartition is only a witness. -/
noncomputable def blocks (H : Finset (Finset V)) : Finset (V × Finset V) :=
  (univ ×ˢ univ.powersetCard 8).filter fun z =>
    ∃ A S, CompleteBlock H z.1 A S ∧ z.2 = A ∪ S

/-- The total number of saturated K4,4 components, counted by center and support. -/
noncomputable def B (H : Finset (Finset V)) : ℕ := (blocks H).card

/-- Saturation identifies a complete block with an entire connected component,
including the absence of edges from its support to the rest of the link. -/
theorem block_component (H : Finset (Finset V)) (hc : CapFour H)
    (c : V) (A S : Finset V) (hb : CompleteBlock H c A S) :
    ((∀ x ∈ A, neighbors H {c, x} = S) ∧
      (∀ y ∈ S, neighbors H {c, y} = A)) ∧
    (∀ x ∈ A ∪ S, ∀ y, (link H c).Adj x y ↔
      (x ∈ A ∧ y ∈ S) ∨ (x ∈ S ∧ y ∈ A)) ∧
    ∃ C : (link H c).ConnectedComponent, C.supp = (↑(A ∪ S) : Set V) := by
  have hn : (∀ x ∈ A, neighbors H {c, x} = S) ∧
      (∀ y ∈ S, neighbors H {c, y} = A) := by
    obtain ⟨hA, hS, hcA, hcS, hAS, hH⟩ := hb
    have sat (A S : Finset V) (hS : S.card = 4) (hcA : c ∉ A) (hcS : c ∉ S)
        (hAS : Disjoint A S) (hH : ∀ x ∈ A, ∀ y ∈ S, ({c, x, y} : Finset V) ∈ H) :
        ∀ x ∈ A, neighbors H {c, x} = S := by
      intro x hx
      have hcx : c ≠ x := by intro h; subst c; exact hcA hx
      have hsub : S ⊆ neighbors H {c, x} := by
        intro y hy
        have hyc : y ≠ c := by intro h; subst y; exact hcS hy
        have hyx : y ≠ x := by intro h; subst y; exact disjoint_left.mp hAS hx hy
        simp only [neighbors, mem_filter, mem_univ, true_and]
        refine ⟨by simp [hyc, hyx], ?_⟩
        have he : insert y ({c, x} : Finset V) = {c, x, y} := by
          ext z; simp only [mem_insert, mem_singleton]; tauto
        rw [he]; exact hH x hx y hy
      exact (eq_of_subset_of_card_le hsub (by
        rw [hS]; exact hc {c, x} (by simp [pairs, hcx]))).symm
    refine ⟨sat A S hS hcA hcS hAS hH, sat S A hA hcS hcA hAS.symm ?_⟩
    intro y hy x hx
    simpa [pair_comm] using hH x hx y hy
  obtain ⟨hA, hS, hcA, hcS, hAS, hH⟩ := hb
  have adjN (x : V) (hcx : c ≠ x) (y : V) :
      (link H c).Adj x y ↔ y ∈ neighbors H {c, x} := by
    have he : insert y ({c, x} : Finset V) = {c, x, y} := by
      ext z; simp only [mem_insert, mem_singleton]; tauto
    simp only [link, neighbors, mem_filter, mem_univ, true_and, mem_insert,
      mem_singleton, not_or, he]
    grind
  have ha : ∀ x ∈ A ∪ S, ∀ y, (link H c).Adj x y ↔
      (x ∈ A ∧ y ∈ S) ∨ (x ∈ S ∧ y ∈ A) := by
    intro x hx y
    rcases mem_union.mp hx with hx | hx
    · have hcx : c ≠ x := by intro h; subst c; exact hcA hx
      have hxs : x ∉ S := fun hs => disjoint_left.mp hAS hx hs
      rw [adjN x hcx y, hn.1 x hx]
      simp [hx, hxs]
    · have hcx : c ≠ x := by intro h; subst c; exact hcS hx
      have hxa : x ∉ A := fun hx' => disjoint_left.mp hAS hx' hx
      rw [adjN x hcx y, hn.2 x hx]
      simp [hx, hxa]
  refine ⟨hn, ha, ?_⟩
  obtain ⟨x₀, hx₀⟩ := card_pos.mp (by omega : 0 < A.card)
  obtain ⟨y₀, hy₀⟩ := card_pos.mp (by omega : 0 < S.card)
  have hxU : x₀ ∈ A ∪ S := mem_union_left _ hx₀
  have hyU : y₀ ∈ A ∪ S := mem_union_right _ hy₀
  have reach (x : V) (hx : x ∈ A ∪ S) : (link H c).Reachable x₀ x := by
    rcases mem_union.mp hx with hx | hx
    · exact ((ha x₀ hxU y₀).mpr (Or.inl ⟨hx₀, hy₀⟩)).reachable.trans
        ((ha y₀ hyU x).mpr (Or.inr ⟨hy₀, hx⟩)).reachable
    · exact ((ha x₀ hxU x).mpr (Or.inl ⟨hx₀, hx⟩)).reachable
  have closed (x y : V) (hx : x ∈ A ∪ S) (hr : (link H c).Reachable x y) : y ∈ A ∪ S := by
    have hr' := ((link H c).reachable_iff_reflTransGen x y).mp hr
    clear hr
    induction hr' with
    | refl => exact hx
    | @tail y z _ hyz ih =>
        rcases (ha y ih z).mp hyz with h | h
        · exact mem_union_right _ h.2
        · exact mem_union_left _ h.2
  refine ⟨(link H c).connectedComponentMk x₀, ?_⟩
  ext x
  constructor
  · intro hx
    exact closed x₀ x hxU ((link H c).connectedComponentMk x₀ |>.reachable_of_mem_supp
      SimpleGraph.ConnectedComponent.connectedComponentMk_mem hx)
  · intro hx
    exact SimpleGraph.ConnectedComponent.sound (reach x hx).symm


/-- A four-edge fiber is a unique four-star and has the reciprocal exact fiber. -/
theorem reciprocal_four_fiber (H : Finset (Finset V)) (hd : DUF H) (hc : CapFour H)
    (S : Finset V) (hS : S.card = 4) (hF : (fiber H S).card = 4) :
    ∃ c A, CompleteBlock H c A S ∧ fiber H S = star c A ∧ fiber H A = star c S ∧
      ∀ d T, d ∉ T → fiber H S = star d T → d = c ∧ T = A := by
  have hne : (fiber H S).Nonempty := card_pos.mp (by omega)
  rcases (fiber_structure H hd hc S hS).2.2 hne with
    ⟨c, A, hcA, hcS, hAS, hFA, hA, hsub⟩ | ⟨T, hT, hFT⟩
  · have hA4 : A.card = 4 := hA.trans hF
    have hb : CompleteBlock H c A S := by
      refine ⟨hA4, hS, hcA, hcS, hAS, ?_⟩
      intro x hx y hy
      have hem : ({c, x} : Finset V) ∈ fiber H S := by
        rw [hFA]; exact mem_image.mpr ⟨x, hx, rfl⟩
      have hym : y ∈ neighbors H {c, x} := (mem_filter.mp hem).2.symm ▸ hy
      have hyH := (mem_filter.mp hym).2.2
      have he : insert y ({c, x} : Finset V) = {c, x, y} := by
        ext z; simp only [mem_insert, mem_singleton]; tauto
      rwa [he] at hyH
    have hpair (d : V) : Function.Injective (fun x : V => ({d, x} : Finset V)) := by
      intro x y hxy
      change ({d, x} : Finset V) = {d, y} at hxy
      have h1 : x ∈ ({d, y} : Finset V) := by rw [← hxy]; simp
      have h2 : y ∈ ({d, x} : Finset V) := by rw [hxy]; simp
      simp only [mem_insert, mem_singleton] at h1 h2
      grind
    have hrec : fiber H A = star c S := by
      apply (eq_of_subset_of_card_le ?_ ?_).symm
      · intro e he
        obtain ⟨y, hy, rfl⟩ := mem_image.mp he
        have hcy : c ≠ y := by intro h; subst c; exact hcS hy
        exact mem_filter.mpr ⟨by simp [pairs, hcy], (block_component H hc c A S hb).1.2 y hy⟩
      · rw [DUFStructure.star, card_image_of_injective _ (hpair c), hS]
        exact (fiber_structure H hd hc A hA4).1
    refine ⟨c, A, hb, hFA, hrec, ?_⟩
    intro d T hdT hdF
    have hdc : d = c := by
      by_contra hdc
      have hsub : A ⊆ {d} := by
        intro x hx
        have hem : ({c, x} : Finset V) ∈ star d T := by
          rw [← hdF, hFA]; exact mem_image.mpr ⟨x, hx, rfl⟩
        obtain ⟨y, hy, he⟩ := mem_image.mp hem
        have : d ∈ ({c, x} : Finset V) := by rw [← he]; simp
        exact mem_singleton.mpr (by simpa [hdc] using this : d = x).symm
      have := card_le_card hsub
      simp only [card_singleton, hA4] at this
      omega
    subst d
    exact ⟨rfl, image_injective (hpair c) (hdF.symm.trans hFA)⟩
  · have : (fiber H S).card = 3 := by rw [hFT, card_powersetCard, hT]; decide
    omega

/-- Conversely, every connected K4,4 link component appears in the center/support count. -/
theorem blocks_iff_component (H : Finset (Finset V)) (hc : CapFour H) (c : V) (U : Finset V) :
    (c, U) ∈ blocks H ↔ ∃ C : (link H c).ConnectedComponent,
      ∃ A S : Finset V, C.supp = (↑U : Set V) ∧ A.card = 4 ∧ S.card = 4 ∧
        Disjoint A S ∧ U = A ∪ S ∧ ∀ x ∈ U, ∀ y, (link H c).Adj x y ↔
          (x ∈ A ∧ y ∈ S) ∨ (x ∈ S ∧ y ∈ A) := by
  constructor
  · intro hmem
    obtain ⟨A, S, hb, hU⟩ := (mem_filter.mp hmem).2
    change U = A ∪ S at hU
    subst U
    obtain ⟨_, ha, C, hC⟩ := block_component H hc c A S hb
    exact ⟨C, A, S, hC, hb.1, hb.2.1, hb.2.2.2.2.1, rfl, ha⟩
  · rintro ⟨C, A, S, hC, hA, hS, hAS, rfl, hadj⟩
    obtain ⟨x₀, hx₀⟩ := card_pos.mp (by omega : 0 < A.card)
    obtain ⟨y₀, hy₀⟩ := card_pos.mp (by omega : 0 < S.card)
    have hca : c ∉ A := by
      intro hca
      have he := (hadj c (mem_union_left _ hca) y₀).mpr (Or.inl ⟨hca, hy₀⟩)
      exact he.2.1 (by simp)
    have hcs : c ∉ S := by
      intro hcs
      have he := (hadj c (mem_union_right _ hcs) x₀).mpr (Or.inr ⟨hcs, hx₀⟩)
      exact he.2.1 (by simp)
    refine mem_filter.mpr ⟨?_, A, S, ⟨hA, hS, hca, hcs, hAS, ?_⟩, rfl⟩
    · simp only [mem_product, mem_univ, true_and, mem_powersetCard, subset_univ]
      rw [card_union_of_disjoint hAS, hA, hS]
    · intro x hx y hy
      exact ((hadj x (mem_union_left _ hx) y).mpr (Or.inl ⟨hx, hy⟩)).2.2

/-- A complete block yields exactly its two reciprocal four-edge fibers. -/
theorem block_fibers (H : Finset (Finset V)) (hd : DUF H) (hc : CapFour H)
    (c : V) (A S : Finset V) (hb : CompleteBlock H c A S) :
    fiber H S = star c A ∧ fiber H A = star c S := by
  have hn := (block_component H hc c A S hb).1
  obtain ⟨hA, hS, hcA, hcS, hAS, hH⟩ := hb
  have hpair : Function.Injective (fun x : V => ({c, x} : Finset V)) := by
    intro x y hxy
    change ({c, x} : Finset V) = {c, y} at hxy
    have h1 : x ∈ ({c, y} : Finset V) := by rw [← hxy]; simp
    have h2 : y ∈ ({c, x} : Finset V) := by rw [hxy]; simp
    simp only [mem_insert, mem_singleton] at h1 h2
    grind
  have he (A S : Finset V) (hA : A.card = 4) (hS : S.card = 4) (hcA : c ∉ A)
      (hn : ∀ x ∈ A, neighbors H {c, x} = S) : fiber H S = star c A := by
    apply (eq_of_subset_of_card_le ?_ ?_).symm
    · intro e he
      obtain ⟨x, hx, rfl⟩ := mem_image.mp he
      have hcx : c ≠ x := by intro h; subst c; exact hcA hx
      exact mem_filter.mpr ⟨by simp [pairs, hcx], hn x hx⟩
    · rw [DUFStructure.star, card_image_of_injective _ hpair, hA]
      exact (fiber_structure H hd hc S hS).1
  exact ⟨he A S hA hS hcA hn.1, he S A hS hA hcS hn.2⟩

end D5.S3.Combinatorics.Graph.DUFComponents
