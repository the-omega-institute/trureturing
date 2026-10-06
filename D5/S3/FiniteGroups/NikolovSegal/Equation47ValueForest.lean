/- GID: D5/S3/FiniteGroups/NikolovSegal/Equation47ValueForest
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Equation47ValueForest
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual finite-group coordinate, extraction or product mathematics. -/

import D5.S3.FiniteGroups.NikolovSegal.Equation47ValueContraction
import Mathlib.Data.List.Sort

set_option autoImplicit false

/-! Part I p.225: the forest labels here are NONBASE VALUE variables after
(50), not commutator witness arcs.  Each variable joins its coordinate to its
actual cycle base.  The forest and its leaf order are derived, componentwise,
from these actual stars. -/
namespace NikolovSegal.Equation47ValueNormalization
open Equation47 Equation47TypeII Equation47WordCoupling
universe u
variable {I : Type u} [Finite I] [DecidableEq I] {m : ℕ}

def valueIncident (tau : Fin m → Equiv.Perm I) (e : Arc m I) (v : I) : Prop :=
  v = e.2 ∨ v = base (tau e.1) e.2

def ValueLeafOrder (tau : Fin m → Equiv.Perm I)
    (L : List (I × Arc m I)) : Prop :=
  (∀ p ∈ L, p.2.2 ≠ base (tau p.2.1) p.2.2 ∧ valueIncident tau p.2 p.1) ∧
    L.Pairwise (fun p s => ¬ valueIncident tau s.2 p.1)

private theorem parent_label (tau : Fin m → Equiv.Perm I)
    {F : SimpleGraph I} (hF : F ≤ valueLinkGraph tau) {v w : I}
    (h : F.Adj v w) : ∃ e : Arc m I,
      (e.2 = v ∧ base (tau e.1) e.2 = w) ∨
      (e.2 = w ∧ base (tau e.1) e.2 = v) := by
  obtain ⟨j,hj | hj⟩ := (hF h).2
  · exact ⟨(j,v),Or.inl ⟨rfl,hj⟩⟩
  · exact ⟨(j,w),Or.inr ⟨rfl,hj⟩⟩

/-- A genuine labelled leaf order of the normalized VALUE forest, with one
root per TRUE component.  Neither powered connectivity nor labels are
assumed.  All labels are actual nonbase values. -/
theorem exists_value_leafOrder [Fintype I] (tau : Fin m → Equiv.Perm I)
    (r : I → I)
    (hr : ∀ v, (qPowerGraph tau 1).Reachable (r v) v)
    (hconst : ∀ v w, (qPowerGraph tau 1).Reachable v w → r v = r w) :
    ∃ (F : SimpleGraph I) (L : List (I × Arc m I)),
      F ≤ valueLinkGraph tau ∧ F.IsAcyclic ∧
      F.Reachable = (qPowerGraph tau 1).Reachable ∧
      ValueLeafOrder tau L ∧
      (∀ v, (∃ p ∈ L, p.1 = v) ↔ v ≠ r v) ∧
      (∀ p ∈ L, F.Adj p.2.2 (base (tau p.2.1) p.2.2)) := by
  classical
  obtain ⟨F,hF,hacyc,hreach⟩ := valueLinkGraph_spanningForest tau
  let d : I → ℕ := fun v => F.dist (r v) v
  have hparent : ∀ v, v ≠ r v → ∃ w, F.Adj v w ∧ d w < d v := by
    intro v hv
    have hrv : F.Reachable (r v) v := by rw [hreach]; exact hr v
    obtain ⟨p,hp,hlen⟩ := hrv.exists_path_of_dist
    have hnil : ¬ p.Nil := p.not_nil_of_ne hv.symm
    have hadj := (p.adj_penultimate hnil).symm
    have hroot : r p.penultimate = r v := hconst _ _ (by
      rw [← valueLinkGraph_reachable]
      exact (hF hadj.symm).reachable)
    refine ⟨p.penultimate,hadj,?_⟩
    have hdist := SimpleGraph.dist_le p.dropLast
    have hlen' := p.length_dropLast_add_one hnil
    dsimp [d]
    rw [hroot]
    omega
  let N := {v : I // v ≠ r v}
  let parent : N → I := fun v => Classical.choose (hparent v v.2)
  have hp : ∀ v : N, F.Adj v.val (parent v) ∧ d (parent v) < d v.val :=
    fun v => Classical.choose_spec (hparent v v.2)
  let edge : N → Arc m I := fun v => Classical.choose (parent_label tau hF (hp v).1)
  have hespec : ∀ v : N,
      ((edge v).2 = v.val ∧ base (tau (edge v).1) (edge v).2 = parent v) ∨
      ((edge v).2 = parent v ∧ base (tau (edge v).1) (edge v).2 = v.val) :=
    fun v => Classical.choose_spec (parent_label tau hF (hp v).1)
  have hend : ∀ (v : N) w,
      valueIncident tau (edge v) w ↔ w = v.val ∨ w = parent v := by
    intro v w
    rcases hespec v with ⟨hs,ht⟩ | ⟨hs,ht⟩
    · unfold valueIncident; rw [ht,hs]
    · unfold valueIncident; rw [ht,hs,or_comm]
  have hlo : ∀ v : N, (edge v).2 ≠ base (tau (edge v).1) (edge v).2 := by
    intro v
    rcases hespec v with ⟨hs,ht⟩ | ⟨hs,ht⟩
    · rw [ht,hs]
      intro h
      have := (hp v).2
      rw [← h] at this
      omega
    · rw [ht,hs]
      intro h
      have := (hp v).2
      rw [h] at this
      omega
  let B : List N := Finset.univ.toList
  let V := B.mergeSort (fun v w => decide (d w.val ≤ d v.val))
  have hmem : ∀ v : N, v ∈ V := by simp [V,B]
  have hnodup : V.Nodup := (List.mergeSort_perm B _).nodup_iff.mpr
    (Finset.nodup_toList _)
  have hsorted : V.Pairwise (fun v w => d w.val ≤ d v.val) := by
    have hh := List.pairwise_mergeSort
      (le := fun v w : N => decide (d w.val ≤ d v.val))
      (by intro a b c; simp only [decide_eq_true_eq]; omega)
      (by intro a b; simp only [Bool.or_eq_true,decide_eq_true_eq]; omega) B
    simpa only [decide_eq_true_eq] using hh
  let f : N → I × Arc m I := fun v => (v.val,edge v)
  refine ⟨F,V.map f,hF,hacyc,hreach,?_,?_,?_⟩
  · constructor
    · intro p hp'
      obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hp'
      exact ⟨hlo v,(hend v v.val).mpr (Or.inl rfl)⟩
    · rw [List.pairwise_map]
      apply (hsorted.and hnodup).imp
      intro v w h
      change ¬ valueIncident tau (edge w) v.val
      rw [hend]
      rintro (hvw | hvp)
      · exact h.2 (Subtype.ext hvw)
      · have hd := (hp w).2
        rw [← hvp] at hd
        omega
  · intro v
    constructor
    · rintro ⟨p,hp',hpv⟩
      obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hp'
      change w.val = v at hpv
      simpa only [hpv] using w.2
    · intro hv
      exact ⟨f ⟨v,hv⟩,List.mem_map.mpr ⟨⟨v,hv⟩,hmem _,rfl⟩,rfl⟩
  · intro p hp'
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hp'
    change F.Adj (edge v).2 (base (tau (edge v).1) (edge v).2)
    rcases hespec v with ⟨hs,ht⟩ | ⟨hs,ht⟩
    · rw [ht,hs]; exact (hp v).1
    · rw [ht,hs]; exact (hp v).1.symm

end NikolovSegal.Equation47ValueNormalization
