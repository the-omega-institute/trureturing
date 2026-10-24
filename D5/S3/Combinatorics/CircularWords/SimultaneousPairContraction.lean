/- GID: D5/S3/Combinatorics/CircularWords/SimultaneousPairContraction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CircularWords/SimultaneousPairContraction
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.List.Cycle]
   utility: none
   digest: Actual contraction equivalences and intersection multiplicities for disjoint paired runs. -/

import D5.S3.Combinatorics.CircularWords.CircleBlockEquivalence

/-! Every contraction preserves all remaining prescribed arcs of the same oriented circle. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.CircularWords.SimultaneousPairContraction

open D5.S3.Combinatorics.CircularWords.DisjointBlockContraction
open D5.S3.Combinatorics.CircularWords.CircularOrderCount
open D5.S3.Combinatorics.CircularWords.CircleBlockEquivalence
open Finset
open scoped Classical

universe u
variable {α : Type u} [DecidableEq α]
noncomputable section

/-- The simultaneous event is an actual finite subset of the oriented circle inventory. -/
def Joint (A : Finset α) (F : Finset (Finset α)) (C : Cycle α) : Prop :=
  C ∈ circles A ∧ ∀ S ∈ F, Arc A S C

/-- One contraction acts on the whole simultaneous event, with expansion as its inverse. -/
noncomputable def jointStepEquiv (A S : Finset α) (F : Finset (Finset α))
    (hS : S ⊆ A) (hs : S.Nonempty) (hv : (A \ S).Nonempty)
    (hF : ∀ T ∈ F, T ⊆ A \ S) (a : α) (ha : a ∈ S) :
    {C : Cycle α // Joint A (insert S F) C} ≃
      ({l : List α // l ∈ orders S} ×
        {D : Cycle α // Joint (contracted A S a) F D}) := by
  let e := blockEquiv A S hS hs hv a ha
  have transfer (z : {l : List α // l ∈ orders S} ×
      {D : Cycle α // D ∈ circles (contracted A S a)}) (T : Finset α) (hT : T ∈ F) :
      Arc A T (e z).val ↔ Arc (contracted A S a) T z.2.val := by
    rw [blockEquiv_expand]
    exact arc_inflate_iff hS (hF T hT) ha (mem_orders.mp z.1.property) z.2.property
  let f : {C : Cycle α // Joint A (insert S F) C} →
      ({l : List α // l ∈ orders S} × {D : Cycle α // Joint (contracted A S a) F D}) :=
    fun C =>
      let z := e.symm ⟨C.val,C.property.2 S (mem_insert_self _ _)⟩
      (z.1,⟨z.2.val,z.2.property,fun T hT => (transfer z T hT).mp (by
        change Arc A T (e (e.symm ⟨C.val,C.property.2 S (mem_insert_self _ _)⟩)).val
        rw [e.apply_symm_apply]
        exact C.property.2 T (mem_insert_of_mem hT))⟩)
  let g : ({l : List α // l ∈ orders S} × {D : Cycle α // Joint (contracted A S a) F D}) →
      {C : Cycle α // Joint A (insert S F) C} := fun z =>
    let z' := (z.1,⟨z.2.val,z.2.property.1⟩)
    let C := e z'
    ⟨C.val,arc_mem_circles hS C.property,by
      intro T hT
      rcases mem_insert.mp hT with rfl|hT
      · exact C.property
      · exact (transfer z' T hT).mpr (z.2.property.2 T hT)⟩
  refine ⟨f,g,?_,?_⟩
  · intro C
    apply Subtype.ext
    change (e (e.symm ⟨C.val,C.property.2 S (mem_insert_self _ _)⟩)).val = C.val
    exact congrArg (fun q : {C : Cycle α // Arc A S C} => q.val) (e.apply_symm_apply _)
  · intro z
    have hh := e.symm_apply_apply (z.1,⟨z.2.val,z.2.property.1⟩)
    apply Prod.ext
    · change (e.symm (e (z.1,⟨z.2.val,z.2.property.1⟩))).1 = z.1
      exact congrArg Prod.fst hh
    · apply Subtype.ext
      change (e.symm (e (z.1,⟨z.2.val,z.2.property.1⟩))).2.val = z.2.val
      exact congrArg (fun q => q.2.val) hh

private theorem joint_empty_card (A : Finset α) (hA : A.Nonempty) :
    Nat.card {C : Cycle α // Joint A ∅ C} = (A.card-1).factorial := by
  let e : {C : Cycle α // Joint A ∅ C} ≃ {C : Cycle α // C ∈ circles A} :=
    Equiv.subtypeEquivRight (fun _ => by simp [Joint])
  rw [Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_coe,circles_card A hA]

/-- All prescribed pair intersections, obtained by composing actual common-circle contractions.
The strict size condition is the range needed for the third Bonferroni truncation. -/
theorem joint_pair_card (A : Finset α) (F : Finset (Finset α))
    (hsub : ∀ S ∈ F, S ⊆ A) (htwo : ∀ S ∈ F, S.card=2)
    (hdisj : (F : Set (Finset α)).Pairwise (fun S T => Disjoint S T)) (hsize : 2*F.card < A.card) :
    Nat.card {C : Cycle α // Joint A F C} =
      2^F.card * (A.card-F.card-1).factorial := by
  induction F using Finset.induction_on generalizing A with
  | empty =>
    simpa using joint_empty_card A (card_pos.mp (by simpa using hsize))
  | @insert S F hSF ih =>
    have hS := hsub S (mem_insert_self _ _)
    have hS2 := htwo S (mem_insert_self _ _)
    have hs : S.Nonempty := card_pos.mp (by omega)
    obtain ⟨a,ha⟩ := hs
    have hF : ∀ T ∈ F, T ⊆ A \ S := by
      intro T hT x hx
      have hST : Disjoint S T := hdisj (mem_insert_self _ _) (mem_insert_of_mem hT)
        (by rintro rfl; exact hSF hT)
      exact mem_sdiff.mpr ⟨hsub T (mem_insert_of_mem hT) hx,
        fun hxs => Finset.disjoint_left.mp hST hxs hx⟩
    have hcard : (contracted A S a).card = A.card-1 := by
      have hna : a ∉ A \ S := by simp [ha]
      rw [contracted,card_insert_of_notMem hna,card_sdiff_of_subset hS,hS2]
      have hh := card_le_card hS
      omega
    have hv : (A \ S).Nonempty := by
      rw [←card_pos,card_sdiff_of_subset hS,hS2]
      rw [card_insert_of_notMem hSF] at hsize
      omega
    have hsub' : ∀ T ∈ F, T ⊆ contracted A S a := by
      intro T hT x hx
      exact mem_insert_of_mem (hF T hT hx)
    have htwo' : ∀ T ∈ F, T.card=2 := fun T hT => htwo T (mem_insert_of_mem hT)
    have hd' : (F : Set (Finset α)).Pairwise (fun S T => Disjoint S T) :=
      hdisj.mono (subset_insert _ _)
    have hz : 2*F.card < (contracted A S a).card := by
      rw [hcard]
      rw [card_insert_of_notMem hSF] at hsize
      omega
    have he := Nat.card_congr (jointStepEquiv A S F hS ⟨a,ha⟩ hv hF a ha)
    rw [he,Nat.card_prod,Nat.card_eq_fintype_card,Fintype.card_coe,orders_card,hS2]
    rw [ih (contracted A S a) hsub' htwo' hd' hz,hcard,card_insert_of_notMem hSF]
    simp only [Nat.factorial_succ,Nat.factorial_zero]
    have hidx : A.card-1-F.card-1 = A.card-(F.card+1)-1 := by omega
    rw [hidx,pow_succ]
    ring

end
end D5.S3.Combinatorics.CircularWords.SimultaneousPairContraction
