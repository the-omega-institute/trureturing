/- GID: D5/S3/Combinatorics/Sequenceability/ZeroTotalCircleGood
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Sequenceability/ZeroTotalCircleGood
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.List.Cycle]
   utility: none
   digest: Zero-total proper-interval Good words are exactly circles with no proper zero arc. -/

import D5.S3.Combinatorics.Sequenceability.PairedZeroSubsetSpectrum
import D5.S3.Combinatorics.CircularWords.CircularOrderCount

/-! The only exempt interval is the full word; zero arcs crossing the seam use their complements. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Sequenceability.ZeroTotalCircleGood

open D5.S3.Combinatorics.Sequenceability.PairedZeroSubsetSpectrum
open D5.S3.Combinatorics.CircularWords.DisjointBlockContraction
open D5.S3.Combinatorics.CircularWords.CircularOrderCount
open Finset
open scoped BigOperators Classical

universe u
variable {G : Type u} [AddCommGroup G] [DecidableEq G]

omit [AddCommGroup G] [DecidableEq G] in
theorem rotated_two_runs {u v w : List G} (h : (u++v).IsRotated w) :
    (∃ p q, w = p++u++q) ∨ (∃ p q, w = p++v++q) := by
  obtain ⟨d,hd,hr⟩ := List.isRotated_iff_mod.mp h
  by_cases hu : d ≤ u.length
  · right
    refine ⟨u.drop d,u.take d,?_⟩
    rw [←hr,List.rotate_eq_drop_append_take hd,List.drop_append,List.take_append]
    simp [Nat.sub_eq_zero_of_le hu,List.append_assoc]
  · left
    have hu : u.length ≤ d := by omega
    refine ⟨v.drop (d-u.length),v.take (d-u.length),?_⟩
    rw [←hr,List.rotate_eq_drop_append_take hd,List.drop_append,List.take_append]
    simp [List.drop_eq_nil_of_le hu,List.take_of_length_le hu,List.append_assoc]

private theorem sum_order {A : Finset G} {w : List G} (hw : w.Perm A.toList) :
    w.sum = ∑ x ∈ A, x := by
  simpa using hw.sum_eq

private theorem nonempty_order {A : Finset G} {w : List G} (hw : w.Perm A.toList)
    (hA : A.Nonempty) : w ≠ [] := by
  apply List.length_pos_iff.mp
  simpa only [hw.length_eq,Finset.length_toList] using hA.card_pos

/-- Every rooting of an actual zero-total circle with a proper zero arc is bad. -/
theorem zero_arc_not_good {A S : Finset G} (hS : S ⊆ A)
    (hS0 : S.Nonempty) (hV0 : (A \ S).Nonempty)
    (hA : ∑ x ∈ A, x = 0) (hZ : ∑ x ∈ S, x = 0)
    {w : List G} (hC : Arc A S (w : Cycle G)) : ¬ Good w := by
  obtain ⟨u,v,hu,hv,hC⟩ := hC
  have hu0 := nonempty_order hu hS0
  have hv0 := nonempty_order hv hV0
  have huz : u.sum = 0 := (sum_order hu).trans hZ
  have hvz : v.sum = 0 := by
    have hh := (sum_order (append_order hS hu hv)).trans hA
    simpa [List.sum_append,huz] using hh
  have hrot := (Cycle.coe_eq_coe.mp hC).symm
  have hlen := hrot.perm.length_eq
  intro hgood
  rcases rotated_two_runs hrot with ⟨p,q,hpq⟩|⟨p,q,hpq⟩
  · have hproper : p ≠ [] ∨ q ≠ [] := by
      by_contra h
      push_neg at h
      rw [hpq,h.1,h.2] at hlen
      simp only [List.nil_append,List.append_nil,List.length_append] at hlen
      have : 0 < v.length := List.length_pos_iff.mpr hv0
      omega
    exact ((good_iff_decomposition w).mp hgood p u q hpq hu0 hproper) huz
  · have hproper : p ≠ [] ∨ q ≠ [] := by
      by_contra h
      push_neg at h
      rw [hpq,h.1,h.2] at hlen
      simp only [List.nil_append,List.append_nil,List.length_append] at hlen
      have : 0 < u.length := List.length_pos_iff.mpr hu0
      omega
    exact ((good_iff_decomposition w).mp hgood p v q hpq hv0 hproper) hvz

/-- On actual zero-total orders, the circular forbidden events exactly express Good. -/
theorem good_iff_no_zero_arc {A : Finset G} (hA : ∑ x ∈ A, x = 0)
    {w : List G} (hw : w ∈ orders A) :
    Good w ↔ ∀ S : Finset G, S ⊆ A → S.Nonempty → (A \ S).Nonempty →
      (∑ x ∈ S, x) = 0 → ¬ Arc A S (w : Cycle G) := by
  constructor
  · intro h S hS hs hv hz ha
    exact zero_arc_not_good hS hs hv hA hz ha h
  · intro h
    apply (good_iff_decomposition w).mpr
    intro l u v he hu hp huz
    let S := u.toFinset
    have hperm := mem_orders.mp hw
    have hnod : (l++u++v).Nodup := he ▸ (hperm.nodup_iff.mpr A.nodup_toList)
    have hun : u.Nodup := (List.nodup_append.mp (List.nodup_append.mp hnod).1).2.1
    have huperm : u.Perm S.toList := by
      apply (List.perm_ext_iff_of_nodup hun S.nodup_toList).mpr
      simp [S]
    have hS : S ⊆ A := by
      intro x hx
      exact mem_toList.mp (hperm.mem_iff.mp (by rw [he]; simp [S] at hx ⊢; tauto))
    have hs : S.Nonempty := by
      obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil u hu
      exact ⟨x,by simpa [S] using hx⟩
    have hwhole : (u++(v++l)).Perm A.toList := by
      apply List.Perm.trans _ hperm
      rw [he]
      have hh : ((u++v)++l).Perm (l++(u++v)) := List.perm_append_comm
      simpa only [List.append_assoc] using hh
    have hk : (v++l).Perm (A \ S).toList := by
      apply (List.perm_append_left_iff S.toList).mp
      exact (huperm.symm.append_right (v++l)).trans
        (hwhole.trans (append_order hS (List.Perm.refl _) (List.Perm.refl _)).symm)
    have hv : (A \ S).Nonempty := by
      have hvl : v++l ≠ [] := by
        intro hnil
        have hv0 : v=[] := List.eq_nil_of_length_eq_zero (by
          have hh := congrArg List.length hnil
          simp only [List.length_append,List.length_nil] at hh
          omega)
        have hl0 : l=[] := List.eq_nil_of_length_eq_zero (by
          have hh := congrArg List.length hnil
          simp only [List.length_append,List.length_nil] at hh
          omega)
        exact hp.elim (fun h => h hl0) (fun h => h hv0)
      have hh := List.length_pos_iff.mpr hvl
      rw [hk.length_eq,Finset.length_toList] at hh
      exact card_pos.mp hh
    have hz : ∑ x ∈ S, x = 0 := (sum_order huperm).symm.trans huz
    apply h S hS hs hv hz
    refine ⟨u,v++l,huperm,hk,?_⟩
    rw [he]
    simpa only [List.append_assoc] using
      (Cycle.coe_eq_coe.mpr (List.isRotated_append (l := l) (l' := u++v)))

end D5.S3.Combinatorics.Sequenceability.ZeroTotalCircleGood
