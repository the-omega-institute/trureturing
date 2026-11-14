/- GID: D5/S3/Combinatorics/Geometry/RowmotionConvexGeodesic
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/RowmotionConvexGeodesic
   mirror-E: none(waiver:abstract-order-identity)
   anchors: []
   utility: none
   digest: Finite order-convex sets admit shortest guarded toggle words in arbitrary posets. -/

import D5.S3.Combinatorics.Geometry.RowmotionEndpointTransport
import Mathlib.Order.Preorder.Finite
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Finset.Dedup

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Geometry.RowmotionConvexGeodesic

open scoped symmDiff
open RowmotionEndpointTransport

universe u
variable {P : Type u} [PartialOrder P]

private lemma erase_extreme (A : Finset P) (hA : (A : Set P).OrdConnected)
    (x : P) (hx : Minimal (· ∈ A) x ∨ Maximal (· ∈ A) x) :
    by classical exact ((A.erase x : Finset P) : Set P).OrdConnected := by
  classical
  constructor
  intro a ha b hb z hz
  have ha' := Finset.mem_erase.mp ha
  have hb' := Finset.mem_erase.mp hb
  apply Finset.mem_erase.mpr
  refine ⟨?_, hA.out ha'.2 hb'.2 hz⟩
  intro hzx
  subst z
  rcases hx with hx | hx
  · exact ha'.1 (le_antisymm hz.1 (hx.2 ha'.2 hz.1))
  · exact hb'.1 (le_antisymm (hx.2 hb'.2 hz.2) hz.2)

private lemma exists_erase (K A : Finset P) (hK : (K : Set P).OrdConnected)
    (hA : (A : Set P).OrdConnected) (hsub : K ⊆ A) (hne : K ≠ A) :
    by classical exact ∃ x ∈ A, x ∉ K ∧ ((A.erase x : Finset P) : Set P).OrdConnected := by
  classical
  obtain ⟨z, hzA, hzK⟩ : ∃ z ∈ A, z ∉ K := by
    by_contra h
    exact hne (Finset.Subset.antisymm hsub (by simpa using h))
  obtain ⟨a, hza, ha⟩ := A.exists_minimal_le hzA
  obtain ⟨b, hzb, hb⟩ := A.exists_le_maximal hzA
  by_cases haK : a ∈ K
  · have hbK : b ∉ K := fun hbK => hzK (hK.out haK hbK ⟨hza, hzb⟩)
    exact ⟨b, hb.1, hbK, erase_extreme A hA b (Or.inr hb)⟩
  · exact ⟨a, ha.1, haK, erase_extreme A hA a (Or.inl ha)⟩

private lemma toggle_erase (A : Finset P) (x : P) (hx : x ∈ A)
    (hA : (A : Set P).OrdConnected)
    (he : by classical exact ((A.erase x : Finset P) : Set P).OrdConnected) :
    by classical exact
      toggle x (A : Set P) = (A.erase x : Set P) ∧
      toggle x (A.erase x : Set P) = (A : Set P) := by
  classical
  have hf : (A : Set P) ∆ {x} = (A.erase x : Set P) := by
    ext y
    by_cases hy : y = x <;> simp [Set.mem_symmDiff, hy, hx]
  have hr : (A.erase x : Set P) ∆ {x} = (A : Set P) := by
    rw [← hf, symmDiff_assoc, symmDiff_self, symmDiff_bot]
  constructor
  · simp only [toggle, hf, if_pos he]
  · simp only [toggle, hr, if_pos hA]

private lemma deletion_word (K A : Finset P) (hK : (K : Set P).OrdConnected)
    (hA : (A : Set P).OrdConnected) (hsub : K ⊆ A) :
    by classical exact ∃ w : List P, w.Nodup ∧ w.toFinset = A \ K ∧
      w.foldl (fun S x => toggle x S) (A : Set P) = (K : Set P) ∧
      w.reverse.foldl (fun S x => toggle x S) (K : Set P) = (A : Set P) := by
  classical
  induction A using Finset.strongInductionOn with
  | H A ih =>
    by_cases hKA : K = A
    · subst A
      exact ⟨[], by simp⟩
    obtain ⟨x, hxA, hxK, he⟩ := exists_erase K A hK hA hsub hKA
    have hKe : K ⊆ A.erase x := by
      intro y hy
      exact Finset.mem_erase.mpr ⟨by intro h; subst y; exact hxK hy, hsub hy⟩
    obtain ⟨v, hvn, hvset, hvf, hvr⟩ := ih (A.erase x) (Finset.erase_ssubset hxA) he hKe
    have hxv : x ∉ v := by
      intro h
      have hh : x ∈ (A.erase x) \ K := hvset ▸ List.mem_toFinset.mpr h
      exact Finset.not_mem_erase x A (Finset.mem_sdiff.mp hh).1
    have hstep := toggle_erase A x hxA hA he
    refine ⟨x :: v, List.nodup_cons.mpr ⟨hxv, hvn⟩, ?_, ?_, ?_⟩
    · rw [List.toFinset_cons, hvset]
      ext y
      by_cases hy : y = x <;> simp [hy, hxA, hxK]
    · simpa only [List.foldl_cons, hstep.1] using hvf
    · simpa only [List.reverse_cons, List.foldl_append, List.foldl_cons,
        List.foldl_nil, hvr] using hstep.2

/-- Every pair of finite ambient order-convex sets has a guarded toggle word using each
point of their symmetric difference exactly once. -/
theorem exists_toggle_word (P : Type u) [PartialOrder P] (s t : Finset P)
    (hs : (s : Set P).OrdConnected) (ht : (t : Set P).OrdConnected) :
    by classical exact ∃ w : List P, w.Nodup ∧ w.toFinset = s ∆ t ∧
      w.length = (s ∆ t).card ∧
      w.foldl (fun A x => RowmotionEndpointTransport.toggle x A) (s : Set P) =
        (t : Set P) := by
  classical
  have hk : ((s ∩ t : Finset P) : Set P).OrdConnected := by
    simpa only [Finset.coe_inter] using hs.inter ht
  obtain ⟨v, hvn, hvs, hvf, _⟩ := deletion_word (s ∩ t) s hk hs Finset.inter_subset_left
  obtain ⟨w, hwn, hws, _, hwr⟩ := deletion_word (s ∩ t) t hk ht Finset.inter_subset_right
  have hn : (v ++ w.reverse).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨hvn, hwn.reverse, ?_⟩
    intro x hxv hxw
    have hx1 : x ∈ s \ (s ∩ t) := hvs ▸ List.mem_toFinset.mpr hxv
    have hx2 : x ∈ t \ (s ∩ t) := hws ▸ List.mem_toFinset.mpr (List.mem_reverse.mp hxw)
    exact (Finset.mem_sdiff.mp hx1).2 (Finset.mem_inter.mpr
      ⟨(Finset.mem_sdiff.mp hx1).1, (Finset.mem_sdiff.mp hx2).1⟩)
  have hset : (v ++ w.reverse).toFinset = s ∆ t := by
    rw [List.toFinset_append, List.toFinset_reverse, hvs, hws]
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter, Finset.mem_symmDiff]
    tauto
  refine ⟨v ++ w.reverse, hn, hset, ?_, ?_⟩
  · rw [← hset, List.toFinset_card_of_nodup hn]
  · rw [List.foldl_append, hvf, hwr]

#print axioms exists_toggle_word

end D5.S3.Combinatorics.Geometry.RowmotionConvexGeodesic
